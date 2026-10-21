"""Entropy-LP engine for sum-difference constants SD(R; -1).

Model.  (X, Y) is an integer-valued, finitely supported pair with X - Y injective on its support.
A configuration is a finite family of vertices g_0, ..., g_{n-1}, each a copy of (X, Y)
(coordinates x_v, y_v), jointly distributed, together with integer linear relations among the
2n coordinates that hold almost surely.  The configuration space L is the solution space of the
relations; a linear form is an integer vector f in Z^{2n}, viewed as a function on L.

Configurations are built from one base vertex by ATTACH steps (copy lemma):
    ATTACH(U, V): U a list of existing vertices, V a list of standard forms of the current
    configuration.  New vertices U' with (U', V) equal in law to (U, V) and U' conditionally
    independent of the whole current configuration given V.  Linear relations transferred:
    tau(f) = f for every U-form f lying in span(cl(V)), where cl is the closure below.

Standard forms of a vertex v: pi_(a,b)(v) = a x_v + b y_v for (a, b) in SLOPES_ALL = R + [(1,-1)].

Closure cl(S) of a set S of standard forms: the smallest set containing S, closed under
  (i)  Q-linear span on L (a form in the Q-span of S is a function of S: values are integers), and
  (ii) injectivity: if x_v - y_v is in the set, so are x_v and y_v.
Both rules are sound: H(cl S) = H(S).

LP variables: h(F) for closed sets F.  Rows: elemental Shannon inequalities over closed sets,
one conditional-independence equality per ATTACH step, equal-law equalities per ATTACH step,
bounds h(pi_r(g_0)) <= 1 for r in R.  Objective: maximize h(g_0).
"""
import sys, time, itertools
import numpy as np
import flint
from math import gcd

P = 536870909  # prime < 2^29, for search-side span tests (the checker is exact)

SLOPE_D = (1, -1)


def prim(v):
    """Primitive integer vector with first nonzero entry positive (projective normal form)."""
    g = 0
    for a in v:
        g = gcd(g, int(a))
    if g == 0:
        return tuple(0 for _ in v)
    w = [int(a) // g for a in v]
    for a in w:
        if a != 0:
            if a < 0:
                w = [-b for b in w]
            break
    return tuple(w)


def int_nullspace(rows, ncols):
    """Integer basis (as list of row vectors) of {z in Q^ncols : r.z = 0 for all rows r}."""
    if len(rows) == 0:
        return [tuple(1 if i == j else 0 for j in range(ncols)) for i in range(ncols)]
    M = flint.fmpz_mat([list(r) for r in rows])
    N, nul = M.nullspace()
    basis = []
    for j in range(nul):
        col = [int(N[i, j]) for i in range(ncols)]
        basis.append(col)
    if not basis:
        return []
    B = flint.fmpz_mat(basis)
    B = B.lll()
    out = []
    for i in range(B.nrows()):
        out.append(tuple(int(B[i, j]) for j in range(B.ncols())))
    return out


def rank_q(rows):
    if len(rows) == 0:
        return 0
    return flint.fmpz_mat([list(r) for r in rows]).rank()


class Config:
    """Exact configuration: n vertices, integer relations on Z^{2n}."""

    def __init__(self, slopes):
        self.R = [tuple(s) for s in slopes]
        self.SL = self.R + [SLOPE_D]
        self.n = 1
        self.rels = []          # integer vectors of length 2n (padded lazily)
        self.steps = []         # list of (U, V, new_vertex_ids)
        self.kinds = []         # per step: None (copy step) or dict(type='link', u, w, link)
        self.parent = [None]    # parent[v'] = v (copy of which vertex), for bookkeeping

    def amb(self, v, s):
        """Ambient vector of the standard form pi_s(v) in Z^{2n}."""
        f = [0] * (2 * self.n)
        f[2 * v] = s[0]
        f[2 * v + 1] = s[1]
        return f

    def basisL(self):
        rels = [list(r) + [0] * (2 * self.n - len(r)) for r in self.rels]
        return int_nullspace(rels, 2 * self.n)  # rows: basis vectors of L (each in Z^{2n})

    def coords(self, B, f):
        """Coordinates of form f restricted to L, w.r.t. basis rows of B: (f.b_1, ..., f.b_d)."""
        return tuple(sum(fi * bi for fi, bi in zip(f, b)) for b in B)

    def standard_forms(self):
        """Distinct normalized standard forms. Returns (E list of coord tuples, idx dict (v,s)->e)."""
        B = self.basisL()
        E, key2e, idx = [], {}, {}
        for v in range(self.n):
            for s in self.SL:
                c = prim(self.coords(B, self.amb(v, s)))
                if all(a == 0 for a in c):
                    raise ValueError("zero form")
                if c not in key2e:
                    key2e[c] = len(E)
                    E.append(c)
                idx[(v, s)] = key2e[c]
        return B, E, idx

    def exact_closure(self, gens, B=None, E=None, idx=None):
        """Exact closure of a list of (v, s) standard forms; returns set of E indices."""
        if B is None:
            B, E, idx = self.standard_forms()
        cur = set(idx[g] for g in gens)
        while True:
            rows = [E[e] for e in cur]
            r = rank_q(rows)
            new = set(cur)
            for e in range(len(E)):
                if e not in new and rank_q(rows + [E[e]]) == r:
                    new.add(e)
            for v in range(self.n):
                if idx[(v, SLOPE_D)] in new:
                    new.add(idx[(v, (1, 0))])
                    new.add(idx[(v, (0, 1))])
            if new == cur:
                return cur
            cur = new

    def attach(self, U, V):
        """ATTACH(U, V). U: list of vertex ids; V: list of (v, s) standard forms."""
        B, E, idx = self.standard_forms()
        d = len(B)
        clV = self.exact_closure(V, B, E, idx)
        W = [E[e] for e in clV]  # spanning set of span(cl V) in L-coordinates
        # U-coordinate forms in L-coordinates
        Ucols = []
        for u in U:
            Ucols.append(self.coords(B, self.amb(u, (1, 0))))
            Ucols.append(self.coords(B, self.amb(u, (0, 1))))
        # alpha in Q^{2|U|} with alpha . Ucols in span(W): alpha.Ucols . N = 0 where N spans W-annihilator
        if W:
            Nrows = int_nullspace(W, d)  # vectors z with w.z = 0 for all w in W
        else:
            Nrows = [tuple(1 if i == j else 0 for j in range(d)) for i in range(d)]
        # matrix M (2|U| x len(Nrows)): M[a][k] = Ucols[a] . Nrows[k]
        M = [[sum(x * y for x, y in zip(Ucols[a], Nrows[k])) for k in range(len(Nrows))]
             for a in range(len(Ucols))]
        # left nullspace of M: alpha with alpha M = 0  <=> M^T alpha = 0
        if len(Nrows) == 0:
            alphas = [tuple(1 if i == j else 0 for j in range(len(Ucols))) for i in range(len(Ucols))]
        else:
            MT = [[M[a][k] for a in range(len(Ucols))] for k in range(len(Nrows))]
            alphas = int_nullspace(MT, len(Ucols))
        n_old = self.n
        newids = list(range(n_old, n_old + len(U)))
        self.n = n_old + len(U)
        for u in U:
            self.parent.append(u)
        newrels = []
        for al in alphas:
            r = [0] * (2 * self.n)
            for a_i, u in enumerate(U):
                ax, ay = al[2 * a_i], al[2 * a_i + 1]
                up = newids[a_i]
                r[2 * u] -= ax
                r[2 * u + 1] -= ay
                r[2 * up] += ax
                r[2 * up + 1] += ay
            if any(r):
                newrels.append(r)
        self.rels = [list(r) + [0] * (2 * self.n - len(r)) for r in self.rels] + newrels
        self.steps.append((list(U), list(V), newids))
        self.kinds.append(None)
        return newids

    def attach_link(self, U, u, w, link):
        """Copy template vertices U (U' ~ U in law), linking template vertex u to current vertex w:
        link = slope (a, b) in R  -> pi_link(u') = pi_link(w);   link = 'id' -> u' = w.
        U' is conditionally independent of the current configuration given the linked forms of w.
        Relations: inherited linear relations of U, plus the link relations."""
        assert u in U and 0 <= w < self.n
        B, E, idx = self.standard_forms()
        d = len(B)
        Ucols = []
        for v in U:
            Ucols.append(self.coords(B, self.amb(v, (1, 0))))
            Ucols.append(self.coords(B, self.amb(v, (0, 1))))
        # alpha with alpha . Ucols = 0 (relations among U coordinates on L)
        MT = [[Ucols[a][k] for a in range(len(Ucols))] for k in range(d)]
        alphas = int_nullspace(MT, len(Ucols)) if d > 0 else [
            tuple(1 if i == j else 0 for j in range(len(Ucols))) for i in range(len(Ucols))]
        n_old = self.n
        newids = list(range(n_old, n_old + len(U)))
        self.n = n_old + len(U)
        for v in U:
            self.parent.append(v)
        newrels = []
        for al in alphas:
            r = [0] * (2 * self.n)
            for a_i, v in enumerate(U):
                vp = newids[a_i]
                r[2 * vp] += al[2 * a_i]
                r[2 * vp + 1] += al[2 * a_i + 1]
            if any(r):
                newrels.append(r)
        up = newids[U.index(u)]
        if link == 'id':
            for c in (0, 1):
                r = [0] * (2 * self.n)
                r[2 * up + c] = 1
                r[2 * w + c] = -1
                newrels.append(r)
            V = [(w, (1, 0)), (w, (0, 1))]
        else:
            a, b = link
            r = [0] * (2 * self.n)
            r[2 * up], r[2 * up + 1] = a, b
            r[2 * w] -= a
            r[2 * w + 1] -= b
            newrels.append(r)
            V = [(w, tuple(link))]
        self.rels = [list(r) + [0] * (2 * self.n - len(r)) for r in self.rels] + newrels
        self.steps.append((list(U), V, newids))
        self.kinds.append(dict(type='link', u=u, w=w, link=link))
        return newids


# ---------------------------------------------------------------------------------------------
# closed-set enumeration (mod P)

def rref_add(basis, piv, vec):
    """Add reduced nonzero vec (mod P) to RREF basis (list of np arrays), return new (basis, piv)."""
    vec = vec % P
    j = int(np.nonzero(vec)[0][0])
    inv = pow(int(vec[j]), P - 2, P)
    vec = (vec * inv) % P
    nb = []
    for b in basis:
        c = int(b[j])
        if c:
            b = (b - c * vec) % P
        nb.append(b)
    nb.append(vec)
    return nb, piv + [j]


def reduce_all(Emod, basis, piv):
    R = Emod.copy()
    for b, j in zip(basis, piv):
        c = R[:, j].copy()
        nz = c != 0
        if nz.any():
            R[nz] = (R[nz] - (c[nz, None] * b[None, :]) % P) % P
    return R


class Lattice:
    def __init__(self, cfg, verbose=True, max_flats=10**7, extra_amb=None):
        """extra_amb: optional list of extra linear forms (ambient integer vectors, length 2n);
        they are added to the ground set as ('amb', k) entries of idx."""
        self.cfg = cfg
        B, E, idx = cfg.standard_forms()
        E = list(E)
        idx = dict(idx)
        self.extra_amb = [tuple(f) for f in extra_amb] if extra_amb else []
        if extra_amb:
            key2e = {e: i for i, e in enumerate(E)}
            for k, f in enumerate(extra_amb):
                c = prim(cfg.coords(B, list(f) + [0] * (2 * cfg.n - len(f))))
                if all(a == 0 for a in c):
                    continue
                if c not in key2e:
                    key2e[c] = len(E)
                    E.append(c)
                idx[('amb', k)] = key2e[c]
        self.B, self.E, self.idx = B, E, idx
        self.m = len(E)
        self.d = len(B)
        self.Emod = np.array([[a % P for a in e] for e in E], dtype=np.int64)
        # injectivity triples (d_e, x_e, y_e)
        tri = set()
        for v in range(cfg.n):
            tri.add((idx[(v, SLOPE_D)], idx[(v, (1, 0))], idx[(v, (0, 1))]))
        self.tri = sorted(tri)
        self.enumerate(verbose, max_flats)

    def _lin_close_mask(self, basis, piv):
        R = reduce_all(self.Emod, basis, piv)
        zero = ~R.any(axis=1)
        mask = 0
        for e in np.nonzero(zero)[0]:
            mask |= 1 << int(e)
        return mask, R

    def _inj_close(self, mask, basis, piv):
        while True:
            add = None
            for (de, xe, ye) in self.tri:
                if (mask >> de) & 1 and not ((mask >> xe) & 1 and (mask >> ye) & 1):
                    add = xe if not (mask >> xe) & 1 else ye
                    break
            if add is None:
                return mask, basis, piv
            r = reduce_all(self.Emod[add:add + 1], basis, piv)[0]
            basis, piv = rref_add(basis, piv, r)
            mask, _ = self._lin_close_mask(basis, piv)

    def enumerate(self, verbose, max_flats):
        t0 = time.time()
        m = self.m
        empty = 0
        self.masks = [empty]
        self.id_of = {empty: 0}
        self.rank = [0]
        self.par = [(-1, -1)]
        bases = {0: ([], [])}
        nxt = []
        q = 0
        while q < len(self.masks):
            F = self.masks[q]
            basis, piv = bases.pop(q)
            R = reduce_all(self.Emod, basis, piv)
            row = np.full(m, q, dtype=np.int64)
            groups = {}
            for e in range(m):
                if (F >> e) & 1:
                    continue
                r = R[e]
                j = int(np.nonzero(r)[0][0])
                inv = pow(int(r[j]), P - 2, P)
                key = ((r * inv) % P).tobytes()
                groups.setdefault(key, []).append(e)
            for key, els in groups.items():
                e0 = els[0]
                nb, npv = rref_add(basis, piv, R[e0])
                mask = F
                for e in els:
                    mask |= 1 << e
                mask, nb, npv = self._inj_close(mask, nb, npv)
                if mask not in self.id_of:
                    self.id_of[mask] = len(self.masks)
                    self.masks.append(mask)
                    self.rank.append(len(npv))
                    self.par.append((q, e0))
                    bases[len(self.masks) - 1] = (nb, npv)
                    if len(self.masks) > max_flats:
                        raise RuntimeError("too many flats")
                fid = self.id_of[mask]
                for e in els:
                    row[e] = fid
            nxt.append(row)
            q += 1
            if verbose and q % 20000 == 0:
                print(f"  flats processed {q}/{len(self.masks)}  {time.time()-t0:.1f}s", flush=True)
        self.nxt = np.array(nxt, dtype=np.int64)
        self.nflats = len(self.masks)
        if verbose:
            print(f"  lattice: m={m} forms, d={self.d}, flats={self.nflats}, {time.time()-t0:.1f}s",
                  flush=True)

    def gens_of(self, f):
        """A generating list of E indices for flat f (from the BFS tree)."""
        out = []
        while f > 0:
            p, e = self.par[f]
            out.append(e)
            f = p
        return out[::-1]

    def rep(self, e):
        """A (v, s) standard form representing E index e."""
        if not hasattr(self, '_rep'):
            self._rep = {}
            std = sorted((key, k) for key, k in self.idx.items() if key[0] != 'amb')
            amb = sorted((key, k) for key, k in self.idx.items() if key[0] == 'amb')
            for key, k in std + amb:
                self._rep.setdefault(k, key)
        return self._rep[e]

    def cl_ids(self, es):
        """Flat id of closure of a set of E indices (via nxt table)."""
        f = 0
        for e in es:
            f = int(self.nxt[f, e])
        return f

    def cl_gens(self, gens):
        return self.cl_ids([self.idx[g] for g in gens])


# ---------------------------------------------------------------------------------------------
# LP rows

class UF:
    def __init__(self, n):
        self.p = list(range(n))

    def find(self, a):
        p = self.p
        while p[a] != a:
            p[a] = p[p[a]]
            a = p[a]
        return a

    def union(self, a, b):
        a, b = self.find(a), self.find(b)
        if a != b:
            if a < b:
                a, b = b, a
            self.p[a] = b
            return True
        return False


def vertex_forms(cfg, v):
    return [(v, s) for s in cfg.SL]


def equal_law_pairs(cfg, lat, verbose=True):
    """Equal-law equalities h(F) = h(G) from every ATTACH step.  Returns list of (F, G, t, gens)."""
    pairs = []
    for t, (U, V, newids) in enumerate(cfg.steps):
        tau = {}
        for u, up in zip(U, newids):
            for s in cfg.SL:
                tau[(u, s)] = (up, s)
        G = []
        for u in U:
            G += vertex_forms(cfg, u)
        Vset = list(V) if cfg.kinds[t] is None else []
        gens_all = G + [g for g in Vset if g not in G]
        img = {g: tau.get(g, g) for g in gens_all}
        # if g in V and also a U-form: as a V-form it is fixed; its tau-image equals it on L anyway.
        for g in Vset:
            img[g] = g
        # BFS over sub-closure-system generated by gens_all
        start = 0
        seen = {0: ()}
        queue = [0]
        gidx = [lat.idx[g] for g in gens_all]
        while queue:
            F = queue.pop()
            gF = seen[F]
            for g, e in zip(gens_all, gidx):
                F2 = int(lat.nxt[F, e])
                if F2 not in seen:
                    seen[F2] = gF + (g,)
                    queue.append(F2)
        for F, gF in seen.items():
            if F == 0:
                continue
            Gimg = lat.cl_gens([img[g] for g in gF])
            if Gimg != F:
                pairs.append((F, Gimg, t, gF))
        if verbose:
            print(f"  step {t}: {len(seen)} closed sets in copy system", flush=True)
    return pairs


def ci_rows(cfg, lat):
    """For each ATTACH step t: h(cl(V u U')) + h(cl(old)) - h(cl(all up to t)) - h(cl(V)) = 0."""
    rows = []
    for t, (U, V, newids) in enumerate(cfg.steps):
        old = list(range(newids[0]))  # vertices existing before step t
        oldg = [g for v in old for g in vertex_forms(cfg, v)]
        newg = [g for v in newids for g in vertex_forms(cfg, v)]
        A = lat.cl_gens(list(V) + newg)
        Bf = lat.cl_gens(oldg)
        J = lat.cl_gens(oldg + newg)
        K = lat.cl_gens(list(V))
        rows.append(((A, 1), (Bf, 1), (J, -1), (K, -1)))
    return rows


def shannon_rows(lat):
    """Elemental inequalities over closed sets. Row (a, b, j, k) means h(a)+h(b)-h(j)-h(k) >= 0;
    monotone rows (a, k) mean h(a) - h(k) >= 0."""
    nxt = lat.nxt
    mono = set()
    sub = set()
    for K in range(lat.nflats):
        covers = sorted(set(int(c) for c in nxt[K]) - {K})
        rep = {}
        for e in range(lat.m):
            c = int(nxt[K, e])
            if c != K and c not in rep:
                rep[c] = e
        for a in covers:
            mono.add((a, K))
        for i in range(len(covers)):
            a = covers[i]
            for j in range(i + 1, len(covers)):
                b = covers[j]
                J = int(nxt[a, rep[b]])
                if J == a or J == b:
                    continue  # reduces to monotonicity
                sub.add((a, b, J, K))
    return mono, sub


def build_and_solve(cfg, lat, verbose=True, use_uf=True, extra_eq=None, solver_opts=None,
                    return_model=False):
    import highspy
    t0 = time.time()
    eqp = equal_law_pairs(cfg, lat, verbose)
    ci = ci_rows(cfg, lat)
    mono, sub = shannon_rows(lat)
    if verbose:
        print(f"  rows: eqlaw {len(eqp)}, ci {len(ci)}, mono {len(mono)}, sub {len(sub)}  "
              f"{time.time()-t0:.1f}s", flush=True)
    nf = lat.nflats
    uf = UF(nf)
    if use_uf:
        for (F, G, t, g) in eqp:
            uf.union(F, G)
    cls = [uf.find(i) for i in range(nf)]
    # column index per class; class of empty set (0) is fixed to zero
    col = {}
    for c in sorted(set(cls)):
        if c == cls[0]:
            continue
        col[c] = len(col)
    ncol = len(col)

    def term(f):
        c = cls[f]
        if c == cls[0]:
            return None
        return col[c]

    rows = []   # (dict col->coef, lo, hi, tag)
    seen = set()

    def addrow(terms, lo, hi, tag):
        dct = {}
        for f, a in terms:
            k = term(f)
            if k is None:
                continue
            dct[k] = dct.get(k, 0) + a
        dct = {k: a for k, a in dct.items() if a != 0}
        if not dct:
            return
        key = (tuple(sorted(dct.items())), lo, hi)
        if key in seen:
            return
        seen.add(key)
        rows.append((dct, lo, hi, tag))

    INF = highspy.kHighsInf
    for (a, k) in mono:
        addrow([(a, 1), (k, -1)], 0, INF, ('mono', a, k))
    for (a, b, J, K) in sub:
        addrow([(a, 1), (b, 1), (J, -1), (K, -1)], 0, INF, ('sub', a, b, J, K))
    for t, r in enumerate(ci):
        addrow(list(r), 0, 0, ('ci', t))
    if not use_uf:
        for (F, G, t, g) in eqp:
            addrow([(F, 1), (G, -1)], 0, 0, ('eq', F, G, t))
    if extra_eq:
        for (F, G) in extra_eq:
            addrow([(F, 1), (G, -1)], 0, 0, ('xeq', F, G))
    bound_rows = []
    for s in cfg.R:
        f = lat.cl_gens([(0, s)])
        bound_rows.append(len(rows))
        addrow([(f, 1)], -INF, 1, ('bound', s))
    obj_f = lat.cl_gens([(0, (1, 0)), (0, (0, 1))])
    if verbose:
        print(f"  LP: {ncol} cols, {len(rows)} rows  {time.time()-t0:.1f}s", flush=True)

    h = highspy.Highs()
    h.setOptionValue("output_flag", bool(verbose and False))
    if solver_opts:
        for k, v in solver_opts.items():
            h.setOptionValue(k, v)
    lp = highspy.HighsLp()
    lp.num_col_ = ncol
    lp.num_row_ = len(rows)
    cost = np.zeros(ncol)
    cost[term(obj_f)] = 1.0
    lp.col_cost_ = cost
    lp.col_lower_ = np.full(ncol, -INF)
    lp.col_upper_ = np.full(ncol, INF)
    lp.row_lower_ = np.array([r[1] for r in rows], dtype=float)
    lp.row_upper_ = np.array([r[2] for r in rows], dtype=float)
    # CSR -> highs uses column-wise by default; build row-wise
    starts, index, value = [0], [], []
    for (dct, lo, hi, tag) in rows:
        for k, a in sorted(dct.items()):
            index.append(k)
            value.append(float(a))
        starts.append(len(index))
    lp.a_matrix_.format_ = highspy.MatrixFormat.kRowwise
    lp.a_matrix_.start_ = np.array(starts, dtype=np.int32)
    lp.a_matrix_.index_ = np.array(index, dtype=np.int32)
    lp.a_matrix_.value_ = np.array(value)
    lp.a_matrix_.num_col_ = ncol
    lp.a_matrix_.num_row_ = len(rows)
    lp.sense_ = highspy.ObjSense.kMaximize
    h.passModel(lp)
    h.run()
    st = h.getModelStatus()
    info = h.getInfo()
    val = info.objective_function_value
    sol = h.getSolution()
    if verbose:
        print(f"  status {h.modelStatusToString(st)}  value {val:.10f}  {time.time()-t0:.1f}s",
              flush=True)
    res = dict(value=val, status=h.modelStatusToString(st), rows=rows, cls=cls, col=col,
               row_dual=np.array(sol.row_dual), col_value=np.array(sol.col_value),
               bound_rows=bound_rows, obj_col=term(obj_f), eqp=eqp, ncol=ncol)
    if return_model:
        res['highs'] = h
    return res
