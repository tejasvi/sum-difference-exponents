"""Entropy-LP engine for the single-set sum-difference exponent (GGSTW 6.43, Tao 3e).

Model.  A is a finite subset of Z, s = log|A|, sigma = log|A+A|, delta = log|A-A|.
Vertex types (declared random variables, all coordinates A-valued):
  'D'  pair (x, y) uniform on a coupling Gamma in A x A with one pair per difference (|Gamma| = |A-A|),
       so x - y determines (x, y) and H(x, y) = delta;
  'U'  single atom uniform on A, H(u) = s;
  'S'  pair (x, y) uniform on a coupling with one pair per sum, so x + y determines (x, y), H(x, y) = sigma;
  'P'  single coordinate copied out of a vertex: A-valued, with the law of the original coordinate.
Steps:
  fresh(t): new vertex of type t independent of everything so far;
  copy(atoms, V): new coordinates with (new, V) equal in law to (atoms, V) and new coordinates conditionally
       independent of everything so far given V (V = list of integer linear forms).  Relations
       transferred: alpha(new) = alpha(old) for every combination alpha of the copied coordinates with
       alpha(old) in span(cl V) + Rel.
Equal-law map of a copy step: tau on W = span(atoms) + span(V) (mod Rel), tau(atom_i) = new_i, tau = id on
V; f and tau(f) have the same law for every f in W.  Special forms (exact rational ambient vectors) are
closed under these maps: atom forms (A-valued), unif forms (uniform on A), D-pairs (law of Gamma),
S-pairs, sum forms ((A+A)-valued), diff forms ((A-A)-valued).
cl(S): smallest set of forms containing S closed under (i) Q-span modulo Rel and (ii) injectivity
(D-pair (a, b): a - b in the set => a, b; S-pair: a + b => a, b).
Support facts: for atom forms z, w: H(z) <= s, H(z + w) <= sigma (z = w allowed), H(z - w) <= delta;
unif forms: H = s; D-pairs: H = delta; S-pairs: H = sigma.
LP: variables h(F) for closed sets of ground forms; elemental Shannon rows; CI rows per step; equal-law
merges (per copy step; optional symmetric-Gamma swaps); bounds; sigma = 1; maximize delta = h(cl{x0,y0}).
"""
import sys, time, itertools
from fractions import Fraction
import numpy as np
import flint
from math import gcd

P = 536870909  # prime for search-side span tests (the checker is exact)


def prim(v):
    """Projective normal form of a rational vector: primitive integer vector, first nonzero positive."""
    den = 1
    for a in v:
        q = Fraction(a).denominator
        den = den * q // gcd(den, q)
    w = [int(Fraction(a) * den) for a in v]
    g = 0
    for a in w:
        g = gcd(g, a)
    if g == 0:
        return tuple(0 for _ in v)
    w = [a // g for a in w]
    for a in w:
        if a != 0:
            if a < 0:
                w = [-b for b in w]
            break
    return tuple(w)


def int_nullspace(rows, ncols):
    """Integer basis (rows) of {z in Q^ncols : r.z = 0 for all rows r} (rows may be rational)."""
    rows = [prim(r) for r in rows if any(r)]
    if len(rows) == 0:
        return [tuple(1 if i == j else 0 for j in range(ncols)) for i in range(ncols)]
    M = flint.fmpz_mat([list(r) for r in rows])
    N, nul = M.nullspace()
    basis = []
    for j in range(nul):
        basis.append([int(N[i, j]) for i in range(ncols)])
    if not basis:
        return []
    B = flint.fmpz_mat(basis).lll()
    return [tuple(int(B[i, j]) for j in range(B.ncols())) for i in range(B.nrows())]


def rank_q(rows):
    rows = [prim(r) for r in rows]
    if len(rows) == 0:
        return 0
    return flint.fmpz_mat([list(r) for r in rows]).rank()


def unit(n, c):
    f = [Fraction(0)] * n
    f[c] = Fraction(1)
    return f


def vlin(*terms):
    """Linear combination of ambient vectors: vlin((c1, v1), (c2, v2), ...)."""
    n = max(len(v) for c, v in terms)
    out = [Fraction(0)] * n
    for c, v in terms:
        for i, a in enumerate(v):
            if a:
                out[i] += c * a
    return out


class Solver:
    """Coefficients of vectors (L-coordinates) in the span of given columns (exact)."""

    def __init__(self, cols, d):
        self.d = d
        I, basis = [], []
        for i, c in enumerate(cols):
            if any(c) and rank_q(basis + [list(c)]) > len(basis):
                basis.append(list(c))
                I.append(i)
        self.I = I
        r = len(I)
        self.r = r
        if r == 0:
            return
        MI = flint.fmpq_mat(d, r)
        for j, i in enumerate(I):
            for a in range(d):
                MI[a, j] = flint.fmpq(Fraction(cols[i][a]).numerator, Fraction(cols[i][a]).denominator)
        rows, sel = [], []
        for a in range(d):
            rr = [cols[i][a] for i in I]
            if rank_q(sel + [rr]) > len(sel):
                sel.append(rr)
                rows.append(a)
            if len(rows) == r:
                break
        R = flint.fmpq_mat(r, r)
        for p, a in enumerate(rows):
            for j in range(r):
                R[p, j] = MI[a, j]
        self.Rinv = R.inv()
        self.rows = rows
        self.MI = MI

    def coeffs_many(self, vecs):
        """For each vector return {col index: Fraction coefficient} or None if not in the span."""
        m = len(vecs)
        if m == 0:
            return []
        if self.r == 0:
            return [({} if not any(v) else None) for v in vecs]
        d, r = self.d, self.r
        G = flint.fmpq_mat(d, m)
        for e, v in enumerate(vecs):
            for a in range(d):
                x = Fraction(v[a])
                if x:
                    G[a, e] = flint.fmpq(x.numerator, x.denominator)
        Gr = flint.fmpq_mat(r, m)
        for p, a in enumerate(self.rows):
            for e in range(m):
                Gr[p, e] = G[a, e]
        Ac = self.Rinv * Gr
        back = self.MI * Ac
        out = []
        for e in range(m):
            if any(back[a, e] != G[a, e] for a in range(d)):
                out.append(None)
                continue
            dct = {}
            for j, i in enumerate(self.I):
                q = Ac[j, e]
                if q != 0:
                    dct[i] = Fraction(int(q.p), int(q.q))
            out.append(dct)
        return out


class Config:
    def __init__(self):
        self.N = 0
        self.vtype = []
        self.vatoms = []
        self.atom_v = []
        self.rels = []
        self.steps = []
        self.sp = dict(atom=[], unif=[], dpair=[], dinj=[], spair=[], sinj=[], sum=[], diff=[])

    # ---- basics -------------------------------------------------------------------------------
    def pad(self, f):
        return [Fraction(a) for a in f] + [Fraction(0)] * (self.N - len(f))

    def basisL(self):
        return int_nullspace(self.rels, self.N)

    def coords(self, B, f):
        f = self.pad(f)
        return tuple(sum((a * b for a, b in zip(f, bb) if a), Fraction(0)) for bb in B)

    def _new_vertex(self, t, k):
        v = len(self.vtype)
        cs = list(range(self.N, self.N + k))
        self.N += k
        self.vtype.append(t)
        self.vatoms.append(cs)
        self.atom_v += [v] * k
        self.rels = [list(r) + [0] * k for r in self.rels]
        for c in cs:
            self.sp['atom'].append(unit(self.N, c))
        if t == 'U':
            self.sp['unif'].append(unit(self.N, cs[0]))
        if t == 'D':
            self.sp['dpair'].append((unit(self.N, cs[0]), unit(self.N, cs[1])))
        if t == 'S':
            self.sp['spair'].append((unit(self.N, cs[0]), unit(self.N, cs[1])))
        return v

    def fresh(self, t):
        k = 2 if t in ('D', 'S') else 1
        v = self._new_vertex(t, k)
        self.steps.append(dict(kind='fresh', type=t, v=v, new=list(self.vatoms[v])))
        return v

    def inj_forms(self):
        out = []
        for a, b in self.sp['dpair'] + self.sp['dinj']:
            out.append((vlin((1, a), (-1, b)), a, b))
        for a, b in self.sp['spair'] + self.sp['sinj']:
            out.append((vlin((1, a), (1, b)), a, b))
        return out

    def closure_coords(self, gens, B):
        cur = [list(g) for g in gens if any(g)]
        r = rank_q(cur) if cur else 0
        inj = [(self.coords(B, c), self.coords(B, a), self.coords(B, b)) for c, a, b in self.inj_forms()]
        while True:
            changed = False
            for (c, a, b) in inj:
                if cur and rank_q(cur + [list(c)]) == r:
                    if rank_q(cur + [list(a), list(b)]) > r:
                        cur = cur + [list(a), list(b)]
                        r = rank_q(cur)
                        changed = True
            if not changed:
                return cur

    # ---- copy step ----------------------------------------------------------------------------
    def copy(self, atoms, V, propagate=True):
        """Copy-lemma step.  atoms: list of coordinates; V: list of forms (ambient vectors, len <= N)."""
        B = self.basisL()
        d = len(B)
        Vc = [self.coords(B, f) for f in V]
        W = self.closure_coords(Vc, B)
        Ucols = [self.coords(B, unit(self.N, c)) for c in atoms]
        Nrows = int_nullspace(W, d) if W else [tuple(1 if i == j else 0 for j in range(d)) for i in range(d)]
        if len(Nrows) == 0:
            alphas = [tuple(1 if i == j else 0 for j in range(len(atoms))) for i in range(len(atoms))]
        else:
            MT = [[sum(x * y for x, y in zip(Ucols[a], Nrows[k])) for a in range(len(atoms))]
                  for k in range(len(Nrows))]
            alphas = int_nullspace(MT, len(atoms))
        Vp = [self.pad(f) for f in V]
        groups = []
        for i, c in enumerate(atoms):
            v = self.atom_v[c]
            for g in groups:
                if g[0] == v:
                    g[1].append(i)
                    break
            else:
                groups.append([v, [i]])
        new = [None] * len(atoms)
        newv = []
        for v, pos in groups:
            t = self.vtype[v]
            if t in ('D', 'S') and len(pos) == 2:
                orig = self.vatoms[v]
                if atoms[pos[0]] == orig[0] and atoms[pos[1]] == orig[1]:
                    nv = self._new_vertex(t, 2)
                    new[pos[0]], new[pos[1]] = self.vatoms[nv]
                    newv.append(nv)
                    continue
                if atoms[pos[0]] == orig[1] and atoms[pos[1]] == orig[0]:
                    nv = self._new_vertex(t, 2)
                    new[pos[1]], new[pos[0]] = self.vatoms[nv]
                    newv.append(nv)
                    continue
            for i in pos:
                nv = self._new_vertex('U' if t == 'U' else 'P', 1)
                new[i] = self.vatoms[nv][0]
                newv.append(nv)
        newrels = []
        for al in alphas:
            r = [0] * self.N
            for i, c in enumerate(atoms):
                r[c] -= al[i]
                r[new[i]] += al[i]
            if any(r):
                newrels.append(r)
        self.rels = [list(r) + [0] * (self.N - len(r)) for r in self.rels] + newrels
        self.steps.append(dict(kind='copy', atoms=list(atoms), V=Vp, new=list(new), newv=newv))
        if propagate:
            self.propagate([len(self.steps) - 1])
        return new

    def rep(self, f, kind='D'):
        """Representative pair: new A-valued atoms (a, b) with a - b = f (kind 'D', f an (A-A)-valued form)
        or a + b = f (kind 'S', f (A+A)-valued); (a, b) is a function of f (one representative per value),
        Gamma-valued, so the difference (sum) determines the pair.  No law information."""
        f = self.pad(f)
        v = len(self.vtype)
        cs = [self.N, self.N + 1]
        self.N += 2
        self.vtype.append('R' + kind)
        self.vatoms.append(cs)
        self.atom_v += [v, v]
        self.rels = [list(r) + [0, 0] for r in self.rels]
        # relation a -/+ b - f = 0, written with integer coefficients
        fr = [Fraction(x) for x in f] + [Fraction(0), Fraction(0)]
        rel = [-x for x in fr]
        rel[cs[0]] += 1
        rel[cs[1]] += (-1 if kind == 'D' else 1)
        den = 1
        for x in rel:
            den = den * x.denominator // gcd(den, x.denominator)
        self.rels.append([int(x * den) for x in rel])
        a, b = unit(self.N, cs[0]), unit(self.N, cs[1])
        self.sp['atom'] += [a, b]
        self.sp['dinj' if kind == 'D' else 'sinj'].append((a, b))
        self.steps.append(dict(kind='rep', type=kind, f=fr[:-2], new=cs))
        return cs

    def copy_vertices(self, vs, V, propagate=True):
        atoms = [c for v in vs for c in self.vatoms[v]]
        return self.copy(atoms, V, propagate)

    # ---- special forms under equal-law maps ---------------------------------------------------
    def step_images(self, t, B, forms):
        """Exact ambient images tau_t(f) (None if f not in W_t)."""
        st = self.steps[t]
        src = [self.coords(B, unit(self.N, c)) for c in st['atoms']]
        fixed = [self.coords(B, f) for f in st['V']]
        amb_img = [unit(self.N, c) for c in st['new']] + [self.pad(f) for f in st['V']]
        S = Solver(src + fixed, len(B))
        out = []
        for co in S.coeffs_many([self.coords(B, f) for f in forms]):
            if co is None:
                out.append(None)
            else:
                out.append(vlin(*[(a, amb_img[i]) for i, a in co.items()]) if co else [Fraction(0)] * self.N)
        return out

    def propagate(self, steps=None, max_rounds=3):
        if steps is None:
            steps = [t for t, st in enumerate(self.steps) if st['kind'] == 'copy']
        for _ in range(max_rounds):
            B = self.basisL()
            changed = False
            for t in steps:
                if self.steps[t]['kind'] != 'copy':
                    continue
                for kind in ('atom', 'unif', 'sum', 'diff'):
                    lst = self.sp[kind]
                    keys = set(tuple(self.coords(B, f)) for f in lst)
                    for im in self.step_images(t, B, lst):
                        if im is None or not any(im):
                            continue
                        k = tuple(self.coords(B, im))
                        if k not in keys:
                            keys.add(k)
                            lst.append(im)
                            changed = True
                for kind in ('dpair', 'dinj', 'spair', 'sinj'):
                    lst = self.sp[kind]
                    keys = set((tuple(self.coords(B, a)), tuple(self.coords(B, b))) for a, b in lst)
                    ia = self.step_images(t, B, [a for a, b in lst])
                    ib = self.step_images(t, B, [b for a, b in lst])
                    for a2, b2 in zip(ia, ib):
                        if a2 is None or b2 is None:
                            continue
                        k = (tuple(self.coords(B, a2)), tuple(self.coords(B, b2)))
                        if k not in keys:
                            keys.add(k)
                            lst.append((a2, b2))
                            changed = True
            if not changed:
                return

    def describe(self):
        s = " ".join(f"{t}{v}:{self.vatoms[v]}" for v, t in enumerate(self.vtype))
        return s + f" | atoms {len(self.sp['atom'])} dpairs {len(self.sp['dpair'])}"


# ---------------------------------------------------------------------------------------------
# closed-set enumeration (mod P), as in search/kakeya/eng.py

def rref_add(basis, piv, vec):
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
    """Ground set: atom forms, pairwise sums and differences of atom forms, virtual sum/diff forms,
    V forms, extras.  Labels per ground element: ('atom',), ('sum',), ('diff',), ('V',), ('extra',)."""

    def __init__(self, cfg, extra=(), verbose=True, max_flats=10 ** 7, pair_filter=None):
        self.cfg = cfg
        B = cfg.basisL()
        self.B = B
        self.d = len(B)
        E, key2e, labels, amb = [], {}, [], []

        def add(f, lab):
            c = cfg.coords(B, f)
            k = prim(c)
            if all(a == 0 for a in k):
                return None
            if k not in key2e:
                key2e[k] = len(E)
                E.append(k)
                labels.append(set())
                amb.append(cfg.pad(f))
            e = key2e[k]
            labels[e].add(lab)
            return e

        atoms = cfg.sp['atom']
        self.atom_e = [add(f, 'atom') for f in atoms]
        self.coord_e = [add(unit(cfg.N, c), 'atom') for c in range(cfg.N)]   # ground index per coordinate
        for i in range(len(atoms)):
            for j in range(i + 1, len(atoms)):
                if pair_filter is not None and not pair_filter(i, j):
                    continue
                add(vlin((1, atoms[i]), (1, atoms[j])), 'sum')
                add(vlin((1, atoms[i]), (-1, atoms[j])), 'diff')
        for f in cfg.sp['sum']:
            add(f, 'sum')
        for f in cfg.sp['diff']:
            add(f, 'diff')
        self.unif_e = [add(f, 'atom') for f in cfg.sp['unif']]
        self.dpair_e, self.spair_e = [], []
        for a, b in cfg.sp['dpair']:
            self.dpair_e.append((add(vlin((1, a), (-1, b)), 'diff'), add(a, 'atom'), add(b, 'atom')))
            add(vlin((1, a), (1, b)), 'sum')
        for a, b in cfg.sp['spair']:
            self.spair_e.append((add(vlin((1, a), (1, b)), 'sum'), add(a, 'atom'), add(b, 'atom')))
            add(vlin((1, a), (-1, b)), 'diff')
        self.inj_e = []
        for a, b in cfg.sp['dinj']:
            self.inj_e.append((add(vlin((1, a), (-1, b)), 'diff'), add(a, 'atom'), add(b, 'atom')))
        for a, b in cfg.sp['sinj']:
            self.inj_e.append((add(vlin((1, a), (1, b)), 'sum'), add(a, 'atom'), add(b, 'atom')))
        for st in cfg.steps:
            if st['kind'] == 'copy':
                for f in st['V']:
                    add(f, 'V')
        for f in extra:
            add(f, 'extra')
        self.E, self.labels, self.amb, self.key2e = E, labels, amb, key2e
        self.extra = [cfg.pad(f) for f in extra]
        self.m = len(E)
        self.Emod = np.array([[a % P for a in e] for e in E], dtype=np.int64)
        self.tri = sorted(set(self.dpair_e + self.spair_e + self.inj_e))
        self.enumerate(verbose, max_flats)

    def form_e(self, f):
        k = prim(self.cfg.coords(self.B, f))
        return self.key2e.get(k)

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
        self.masks = [0]
        self.id_of = {0: 0}
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
        out = []
        while f > 0:
            p, e = self.par[f]
            out.append(e)
            f = p
        return out[::-1]

    def cl_ids(self, es):
        f = 0
        for e in es:
            f = int(self.nxt[f, e])
        return f

    def cl_forms(self, forms):
        es = []
        for f in forms:
            e = self.form_e(f)
            if e is None:
                raise ValueError("form not in ground set")
            es.append(e)
        return self.cl_ids(es)


# ---------------------------------------------------------------------------------------------
# merges (equal-law identifications)

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


def merge_gens(lat, src, img, fixed):
    """Generators (e, e_img) of an equal-law map tau (src -> img, fixed pointwise), L-coordinates."""
    cols = list(src) + list(fixed)
    imgs = list(img) + list(fixed)
    S = Solver(cols, lat.d)
    gens = []
    for e, co in enumerate(S.coeffs_many(lat.E)):
        if co is None or not co:
            continue
        v = [Fraction(0)] * lat.d
        for i, a in co.items():
            for j in range(lat.d):
                if imgs[i][j]:
                    v[j] += a * imgs[i][j]
        if not any(v):
            continue
        e2 = lat.key2e.get(prim(v))
        if e2 is not None:
            gens.append((e, e2))
    return gens


def sub_system_merges(lat, gens):
    seen = {0: ()}
    queue = [0]
    while queue:
        F = queue.pop()
        gF = seen[F]
        for gi, (e, e2) in enumerate(gens):
            F2 = int(lat.nxt[F, e])
            if F2 not in seen:
                seen[F2] = gF + (gi,)
                queue.append(F2)
    out = []
    for F, gF in seen.items():
        if F == 0:
            continue
        G = lat.cl_ids([gens[gi][1] for gi in gF])
        if G != F:
            out.append((F, G, [gens[gi][0] for gi in gF]))
    return out


def all_maps(cfg, lat, sym_gamma=False):
    B = lat.B
    maps = []
    for t, st in enumerate(cfg.steps):
        if st['kind'] == 'copy':
            src = [cfg.coords(B, unit(cfg.N, c)) for c in st['atoms']]
            img = [cfg.coords(B, unit(cfg.N, c)) for c in st['new']]
            fixed = [cfg.coords(B, f) for f in st['V']]
            maps.append((('step', t), merge_gens(lat, src, img, fixed)))
    if sym_gamma:
        for k, (a, b) in enumerate(cfg.sp['dpair']):
            ca, cb = cfg.coords(B, a), cfg.coords(B, b)
            maps.append((('swap', k), merge_gens(lat, [ca, cb], [cb, ca], [])))
    return maps


def ci_rows(cfg, lat):
    rows = []
    for t, st in enumerate(cfg.steps):
        if st['kind'] == 'rep':
            continue
        new = st['new']
        old = list(range(min(new)))
        if not old:
            continue
        V = st['V'] if st['kind'] == 'copy' else []
        olde = [lat.coord_e[c] for c in old]
        newe = [lat.coord_e[c] for c in new]
        Ve = []
        for f in V:
            e = lat.form_e(f)
            if e is None:
                raise ValueError("V form not ground")
            Ve.append(e)
        A = lat.cl_ids(Ve + newe)
        Bf = lat.cl_ids(olde)
        J = lat.cl_ids(olde + newe)
        K = lat.cl_ids(Ve)
        rows.append((t, ((A, 1), (Bf, 1), (J, -1), (K, -1))))
    return rows


# ---------------------------------------------------------------------------------------------
# LP

def shannon_arrays(lat):
    nxt = lat.nxt
    nf, m = nxt.shape
    A, B, J, K = [], [], [], []
    MA, MK = [], []
    for k in range(nf):
        row = nxt[k]
        u, first = np.unique(row, return_index=True)
        sel = u != k
        cov = u[sel]
        rep = first[sel]
        if cov.size == 0:
            continue
        MA.append(cov)
        MK.append(np.full(cov.size, k))
        if cov.size < 2:
            continue
        Jm = nxt[cov[:, None], rep[None, :]]
        ii, jj = np.triu_indices(cov.size, 1)
        jv = Jm[ii, jj]
        ok = (jv != cov[ii]) & (jv != cov[jj])
        if ok.any():
            A.append(cov[ii[ok]])
            B.append(cov[jj[ok]])
            J.append(jv[ok])
            K.append(np.full(int(ok.sum()), k))
    cat = lambda L: np.concatenate(L) if L else np.zeros(0, dtype=np.int64)
    return cat(MA), cat(MK), cat(A), cat(B), cat(J), cat(K)


def build_lp(cfg, lat, sym_gamma=False, verbose=False, use_s=True, use_diff=True, extra_rows=None,
             plunnecke=None):
    """plunnecke: optional list of (ambient form, p, m): f is a sum of p atom forms minus m atom forms (any
    coupling), so f lies in pA - mA and H(f) <= (p+m) sigma - (p+m-1) s (Pluennecke-Ruzsa)."""
    import scipy.sparse as sp
    t0 = time.time()
    maps = all_maps(cfg, lat, sym_gamma)
    merges = []
    for tag, gens in maps:
        for (F, G, gF) in sub_system_merges(lat, gens):
            merges.append((tag, F, G, gF))
    uf = UF(lat.nflats)
    for (tag, F, G, gF) in merges:
        uf.union(F, G)
    cls = np.array([uf.find(i) for i in range(lat.nflats)], dtype=np.int64)
    zc = cls[0]
    uniq = np.unique(cls)
    uniq = uniq[uniq != zc]
    pos = {int(c): i for i, c in enumerate(uniq)}
    colof = np.array([pos.get(int(c), -1) for c in cls], dtype=np.int64)
    ncol = len(uniq)
    MA, MK, A, B, J, K = shannon_arrays(lat)
    ca, ck = colof[MA], colof[MK]
    keep = ca != ck
    mono = np.stack([ca[keep], ck[keep]], 1) if keep.any() else np.zeros((0, 2), dtype=np.int64)
    mono_tag = np.stack([MA[keep], MK[keep]], 1) if keep.any() else np.zeros((0, 2), dtype=np.int64)
    if len(mono):
        mono, mi = np.unique(mono, axis=0, return_index=True)
        mono_tag = mono_tag[mi]
    p = np.sort(np.stack([colof[A], colof[B]], 1), 1)
    q = np.sort(np.stack([colof[J], colof[K]], 1), 1)
    sub_tag = np.stack([A, B, J, K], 1)
    rowsP, rowsQ = p.copy(), q.copy()
    for i in range(2):
        for j in range(2):
            mt = (rowsP[:, i] == rowsQ[:, j]) & (rowsP[:, i] != -2)
            rowsP[mt, i] = -2
            rowsQ[mt, j] = -2
    key = np.concatenate([np.sort(rowsP, 1), np.sort(rowsQ, 1)], 1)
    nontriv = ~np.all(np.isin(key, [-1, -2]), axis=1)
    key, sub_tag = key[nontriv], sub_tag[nontriv]
    if len(key):
        key, si = np.unique(key, axis=0, return_index=True)
        sub_tag = sub_tag[si]
    ri, rj, rv, lo, hi = [], [], [], [], []
    r = 0
    INF = np.inf
    nm = len(mono)
    if nm:
        ar = np.arange(nm)
        ok0 = mono[:, 0] >= 0
        ok1 = mono[:, 1] >= 0
        ri += [ar[ok0], ar[ok1]]
        rj += [mono[ok0, 0], mono[ok1, 1]]
        rv += [np.ones(int(ok0.sum())), -np.ones(int(ok1.sum()))]
        r = nm
    lo += [0.0] * nm
    hi += [INF] * nm
    ns = len(key)
    if ns:
        idx = np.arange(r, r + ns)
        for c, sgn in [(0, 1.0), (1, 1.0), (2, -1.0), (3, -1.0)]:
            colv = key[:, c]
            ok = colv >= 0
            ri.append(idx[ok])
            rj.append(colv[ok])
            rv.append(np.full(int(ok.sum()), sgn))
        r += ns
    lo += [0.0] * ns
    hi += [INF] * ns

    def addrow(dct, l, h):
        nonlocal r
        d = {}
        for f, a in dct:
            c = colof[f]
            if c >= 0:
                d[c] = d.get(c, 0) + a
        d = {c: a for c, a in d.items() if a != 0}
        if not d:
            if l <= 0 <= h:
                return False
            raise RuntimeError("infeasible constant row")
        ri.append(np.full(len(d), r))
        rj.append(np.array(list(d.keys()), dtype=np.int64))
        rv.append(np.array(list(d.values()), dtype=float))
        lo.append(l)
        hi.append(h)
        r += 1
        return True

    ci = ci_rows(cfg, lat)
    ci_start = r
    ci_tags = []
    for t, row in ci:
        if addrow(list(row), 0.0, 0.0):
            ci_tags.append(t)
    nci = r - ci_start
    x0, y0 = lat.coord_e[0], lat.coord_e[1]
    obj_f = lat.cl_ids([x0, y0])
    s_f = None
    if lat.unif_e:
        s_f = int(lat.nxt[0, lat.unif_e[0]])
    bstart = r
    btags = []
    for e, labs in enumerate(lat.labels):
        f = int(lat.nxt[0, e])
        if 'sum' in labs or 'atom' in labs:
            if addrow([(f, 1)], -INF, 1.0):
                btags.append(('sum', e))
        if 'diff' in labs and use_diff:
            if addrow([(f, 1), (obj_f, -1)], -INF, 0.0):
                btags.append(('diff', e))
        if 'atom' in labs and use_s and s_f is not None:
            if addrow([(f, 1), (s_f, -1)], -INF, 0.0):
                btags.append(('atom', e))
    for k, e in enumerate(lat.unif_e):
        f = int(lat.nxt[0, e])
        if s_f is not None and addrow([(f, 1), (s_f, -1)], 0.0, 0.0):
            btags.append(('unif', k))
    for k, (de, xe, ye) in enumerate(lat.dpair_e):
        f = lat.cl_ids([xe, ye])
        if addrow([(f, 1), (obj_f, -1)], 0.0, 0.0):
            btags.append(('dpair', k))
    for k, (se, xe, ye) in enumerate(lat.spair_e):
        f = lat.cl_ids([xe, ye])
        if addrow([(f, 1)], 1.0, 1.0):
            btags.append(('spair', k))
    if plunnecke and s_f is not None:
        for (f, p, m) in plunnecke:
            e = lat.form_e(f)
            if e is None:
                continue
            fl = int(lat.nxt[0, e])
            k = p + m
            if addrow([(fl, 1), (s_f, k - 1)], -INF, float(k)):
                btags.append(('plun', e, p, m))
    nb = r - bstart
    xstart = r
    if extra_rows:
        for (dct, l, h) in extra_rows(lat):
            addrow(list(dct.items()), l, h)
    nx = r - xstart
    Amat = sp.csr_matrix((np.concatenate(rv), (np.concatenate(ri), np.concatenate(rj))), shape=(r, ncol))
    if verbose:
        print(f"  LP: {ncol} cols, {r} rows (mono {nm}, sub {ns}, ci {nci}, bounds {nb}, extra {nx}), "
              f"merges {len(merges)}, {time.time()-t0:.2f}s", flush=True)
    return dict(A=Amat, lo=np.array(lo), hi=np.array(hi), ncol=ncol, nm=nm, ns=ns, nci=nci,
                mono_tag=mono_tag, sub_tag=sub_tag, ci_start=ci_start, ci_tags=ci_tags, bstart=bstart,
                nb=nb, btags=btags, xstart=xstart, nx=nx, obj_col=int(colof[obj_f]), obj_f=obj_f,
                s_f=s_f, colof=colof, cls=cls, merges=merges)


IPM = dict(solver="ipm", run_crossover="off", threads=1)
IPMX = dict(solver="ipm", threads=1)


def solve_lp(L, opts=None):
    import highspy
    h = highspy.Highs()
    h.setOptionValue("output_flag", False)
    if opts:
        for k, v in opts.items():
            h.setOptionValue(k, v)
    A = L['A']
    lp = highspy.HighsLp()
    lp.num_col_ = L['ncol']
    lp.num_row_ = A.shape[0]
    c = np.zeros(L['ncol'])
    c[L['obj_col']] = 1.0
    lp.col_cost_ = c
    INF = highspy.kHighsInf
    lp.col_lower_ = np.full(L['ncol'], -INF)
    lp.col_upper_ = np.full(L['ncol'], INF)
    lo = L['lo'].copy()
    hi = L['hi'].copy()
    lo[np.isinf(lo)] = -INF
    hi[np.isinf(hi)] = INF
    lp.row_lower_ = lo
    lp.row_upper_ = hi
    lp.a_matrix_.format_ = highspy.MatrixFormat.kRowwise
    lp.a_matrix_.start_ = A.indptr.astype(np.int32)
    lp.a_matrix_.index_ = A.indices.astype(np.int32)
    lp.a_matrix_.value_ = A.data.astype(float)
    lp.a_matrix_.num_col_ = L['ncol']
    lp.a_matrix_.num_row_ = A.shape[0]
    lp.sense_ = highspy.ObjSense.kMaximize
    h.passModel(lp)
    h.run()
    st = h.modelStatusToString(h.getModelStatus())
    val = h.getInfo().objective_function_value
    sol = h.getSolution()
    return dict(value=val, status=st, row_dual=np.array(sol.row_dual), col_value=np.array(sol.col_value))


def evaluate(cfg, extra=(), sym_gamma=False, verbose=False, max_flats=300000, opts=IPM, pair_filter=None,
             **kw):
    lat = Lattice(cfg, extra=extra, verbose=verbose, max_flats=max_flats, pair_filter=pair_filter)
    L = build_lp(cfg, lat, sym_gamma=sym_gamma, verbose=verbose, **kw)
    S = solve_lp(L, opts=opts)
    return S, L, lat


def F(cfg, dct):
    """Ambient form from a sparse dict {coordinate: coefficient}."""
    f = [Fraction(0)] * cfg.N
    for c, a in dct.items():
        f[c] = Fraction(a)
    return f
