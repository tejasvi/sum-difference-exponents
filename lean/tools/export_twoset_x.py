#!/usr/bin/env python3
"""Export a two-set exponent certificate (check3.py format) as Lean modules, with the row types pmerge and xshare.

Usage: python3 -I tools/export_twoset_x.py CERT.json NAME [--rows-per-file N] [--ids-per-file N]

This is tools/export_twoset.py (unchanged, still used for the earlier certificates) with three additions: the snapshot
tools/ref/check3_8ab8e59a.py (check3.py with the pmerge and xshare rows) replaces tools/ref/check3.py; rows of type
pmerge and xshare are exported (see `copy_map`); and the generated TorsionFree.lean states the pair ceiling for finite
subsets of torsion-free abelian groups (`card_sub_le_of_int`).

Writes EntropyBounds/TwoSet/Certs/NAME/{Defs,Ids_k,Rows_k,Final,Headline,TorsionFree}.lean.  The certificate is untrusted data: every row
becomes a Lean lemma proved from the generic lemmas of EntropyBounds/Iid and EntropyBounds/TwoSet/Common, and the
final step is an exact `linear_combination` with the certificate's multipliers.  The exporter re-derives the row
semantics with check3.py (snapshot in tools/ref/check3.py) and checks the final identity exactly before writing.

Model: every W vertex with law mu^{*i} nu^{*j} is realised by i + j fresh copies of (X1, Y1) (w = sum of i x- and
j y-coordinates of fresh copies; the joint law of all vertices is unchanged), so all rows are statements about m iid
copies (Lean `HLm Γ m`).  Closure classes (check3's closure_key) get one representative list each; every other
generator list gets an identity lemma with explicit determination witnesses (checked by `decide`).
"""
import sys, os, json, math, argparse, hashlib
from fractions import Fraction as Fr

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "ref"))
import check3_8ab8e59a as check3  # noqa: E402  (read-only snapshot of check3.py, sha256 8ab8e59a...)

ROOT = os.path.dirname(HERE)

# ----------------------------------------------------------------------------------------------------------------
# configuration


class Cfg:
    def __init__(self, C):
        assert 'configs' not in C, "multi-configuration certificates are not supported yet"
        cf = C['config']
        self.N = int(cf['coords'])
        self.dv, self.wv = [], []
        for v in cf['vertices']:
            cs = [int(c) for c in v['coords']]
            if v['type'] == 'D':
                self.dv.append((cs[0], cs[1]))
            elif v['type'] == 'W':
                self.wv.append((cs[0], int(v['ij'][0]), int(v['ij'][1])))
            else:
                raise ValueError("vertex type %r not supported yet" % v['type'])
        self.vtypes = [v['type'] for v in cf['vertices']]
        self.vcoords = [sorted(int(c) for c in v['coords']) for v in cf['vertices']]
        # Lean vertices: D vertices first (in order), then the fresh copies of the W vertices
        self.coordmap = {}          # certificate coordinate -> list of (lean vertex, 0 for x / 1 for y)
        for t, (x, y) in enumerate(self.dv):
            self.coordmap[x] = [(t, 0)]
            self.coordmap[y] = [(t, 1)]
        nxt = len(self.dv)
        self.wfresh = {}            # W coordinate -> list of its fresh lean vertices (x-part then y-part)
        for (w, a, b) in self.wv:
            lst = []
            for _ in range(a):
                lst.append((nxt, 0)); nxt += 1
            for _ in range(b):
                lst.append((nxt, 1)); nxt += 1
            assert lst, "W vertex with ij = (0,0)"
            self.coordmap[w] = lst
            self.wfresh[w] = [k for k, _ in lst]
        self.m = nxt
        self.nD = len(self.dv)
        # check3 globals
        check3.NC = self.N
        check3.DV[:] = list(self.dv)
        check3.WV[:] = list(self.wv)
        check3.CV[:] = []

    def lean_form(self, v):
        """certificate form (list of N Fractions) -> lean form (tuple of m (int, int) pairs)."""
        assert len(v) == self.N
        acc = [[0, 0] for _ in range(self.m)]
        for c, a in enumerate(v):
            if a == 0:
                continue
            assert Fr(a).denominator == 1, "non-integer form coefficient %r" % (a,)
            for (k, comp) in self.coordmap[c]:
                acc[k][comp] += int(a)
        return tuple((p[0], p[1]) for p in acc)


# ----------------------------------------------------------------------------------------------------------------
# exact linear algebra in lean coordinates (flat vectors of length 2m)

def flat(f):
    return [Fr(x) for p in f for x in p]


def unflat(v, m):
    return tuple((int(v[2 * k]), int(v[2 * k + 1])) for k in range(m))


def express(target, vecs):
    """Rational coefficients mu with sum mu_i vecs_i = target, or None."""
    n = len(vecs)
    rows = []          # (pivot, vec, combo)
    for i, v in enumerate(vecs):
        v = list(v)
        combo = [Fr(0)] * n
        combo[i] = Fr(1)
        for (p, rv, rc) in rows:
            if v[p] != 0:
                cf = v[p] / rv[p]
                v = [a - cf * b for a, b in zip(v, rv)]
                combo = [a - cf * b for a, b in zip(combo, rc)]
        piv = next((j for j, a in enumerate(v) if a != 0), None)
        if piv is None:
            continue
        rows.append((piv, v, combo))
    t = list(target)
    res = [Fr(0)] * n
    for (p, rv, rc) in rows:
        if t[p] != 0:
            cf = t[p] / rv[p]
            t = [a - cf * b for a, b in zip(t, rv)]
            res = [a + cf * b for a, b in zip(res, rc)]
    if any(a != 0 for a in t):
        return None
    return res


def in_span(target, vecs):
    return express(target, vecs) is not None


def lcm_den(xs):
    d = 1
    for x in xs:
        d = d * Fr(x).denominator // math.gcd(d, Fr(x).denominator)
    return d


def primitive(v):
    """scale a rational vector to a primitive integer vector with positive leading entry."""
    d = lcm_den(v)
    w = [int(x * d) for x in v]
    g = 0
    for x in w:
        g = math.gcd(g, abs(x))
    if g == 0:
        return w
    w = [x // g for x in w]
    lead = next(x for x in w if x != 0)
    if lead < 0:
        w = [-x for x in w]
    return w


# ----------------------------------------------------------------------------------------------------------------

class Exporter:
    def __init__(self, C, name):
        self.C = C
        self.name = name
        self.cfg = Cfg(C)
        self.m = self.cfg.m
        self.forms = {}         # lean form -> name
        self.lists = {}         # tuple of lean forms -> name
        self.list_order = []
        self.form_order = []
        self.rep_of_key = {}    # closure key (lean space) -> representative list tuple
        self.ids = {}           # list tuple -> (identity lemma name, rep tuple) or ('zero',) or ('rep',)
        self.id_order = []
        self.id_text = []

    # --- registries
    def F(self, f):
        if f not in self.forms:
            self.forms[f] = "F%d" % len(self.forms)
            self.form_order.append(f)
        return self.forms[f]

    def L(self, lst):
        lst = tuple(lst)
        if not lst:
            return "([] : List (Form %d))" % self.m
        for f in lst:
            self.F(f)
        if lst not in self.lists:
            self.lists[lst] = "L%d" % len(self.lists)
            self.list_order.append(lst)
        return self.lists[lst]

    # --- closure in lean space (D vertices only, as check3)
    def dvec(self, k):
        v = [Fr(0)] * (2 * self.m)
        v[2 * k] = Fr(1); v[2 * k + 1] = Fr(-1)
        return v

    def unit(self, k, comp):
        v = [Fr(0)] * (2 * self.m)
        v[2 * k + comp] = Fr(1)
        return v

    def rounds(self, lst):
        """closure rounds: list of lists S_0 = lst, S_1, ... (each adds x_k, y_k for newly determined k)."""
        S = [flat(f) for f in lst]
        out = [list(S)]
        while True:
            new = []
            for k in range(self.cfg.nD):
                if in_span(self.dvec(k), S) and not (in_span(self.unit(k, 0), S) and in_span(self.unit(k, 1), S)):
                    new.append(k)
            if not new:
                break
            for k in new:
                S = S + [self.unit(k, 0), self.unit(k, 1)]
            out.append(list(S))
        return out

    def closure_key(self, lst):
        S = self.rounds(lst)[-1]
        rows = check3.rref(S) if S else []
        return tuple(tuple(r) for p, r in rows)

    def rep(self, key):
        if key not in self.rep_of_key:
            vecs = [primitive(list(r)) for r in key]
            self.rep_of_key[key] = tuple(unflat(v, self.m) for v in vecs)
        return self.rep_of_key[key]

    # --- witnesses
    def dw_one(self, S, f):
        """one-round determination witness of f from S (lists of flat vectors), or None."""
        gens = [k for k in range(self.cfg.nD) if in_span(self.dvec(k), S)]
        aug = list(S) + [self.unit(k, c) for k in gens for c in (0, 1)]
        mu = express(flat(f) if isinstance(f, tuple) else f, aug)
        if mu is None:
            return None
        c = lcm_den(mu)
        ms = [int(x * c) for x in mu[:len(S)]]
        g = [[0, 0] for _ in range(self.m)]
        for idx, k in enumerate(gens):
            g[k][0] = int(mu[len(S) + 2 * idx] * c)
            g[k][1] = int(mu[len(S) + 2 * idx + 1] * c)
        wc = [1] * self.m
        wit = [[] for _ in range(self.m)]
        for k in range(self.m):
            if g[k] != [0, 0]:
                nu = express(self.dvec(k), S)
                d = lcm_den(nu)
                wc[k] = d
                wit[k] = [int(x * d) for x in nu]
        return (c, ms, tuple((a, b) for a, b in g), wc, wit)

    def dw_text(self, w):
        c, ms, g, wc, wit = w
        gs = "![" + ", ".join("(%d, %d)" % p for p in g) + "]"
        wcs = "![" + ", ".join(str(x) for x in wc) + "]"
        wits = "![" + ", ".join("[" + ", ".join(str(x) for x in wl) + "]" for wl in wit) + "]"
        return "⟨%d, [%s], %s, %s, %s⟩" % (c, ", ".join(str(x) for x in ms), gs, wcs, wits)

    def dws(self, S, T):
        """witnesses for every form of T (tuple of lean forms) from S (tuple of lean forms), one round."""
        Sv = [flat(f) for f in S]
        out = []
        for f in T:
            w = self.dw_one(Sv, f)
            assert w is not None, "form not determined in one round"
            out.append(self.dw_text(w))
        return "[" + ", ".join(out) + "]"

    def identity(self, lst):
        """make sure HLm of lst is rewritten to its representative; returns ('rep',), ('zero', name) or ('id', name)."""
        lst = tuple(lst)
        if lst in self.ids:
            return self.ids[lst]
        key = self.closure_key(lst)
        if not key:
            # empty closure: every form is zero
            if len(lst) == 0:
                res = ('nil',)
            else:
                nm = "z%d" % len(self.id_order)
                Ln = self.L(lst)
                self.id_text.append(
                    "theorem %s {Γ : Finset (ℤ × ℤ)} (hΓ : Γ.Nonempty) (hinj : Inj Γ) : HLm Γ %d %s = 0 :=\n"
                    "  HLm_eq_zero_wit hΓ hinj %s %s (by decide)\n" % (nm, self.m, Ln, Ln, self.dws((), lst)))
                self.id_order.append(nm)
                res = ('zero', nm)
            self.ids[lst] = res
            return res
        R = self.rep(key)
        self.L(R)
        if R == lst:
            res = ('rep',)
            self.ids[lst] = res
            return res
        rs = self.rounds(lst)
        chain = [lst]
        for S in rs[1:-1]:
            chain.append(tuple(unflat(v, self.m) for v in S))
        chain.append(R)
        steps = []
        for a, b in zip(chain[:-1], chain[1:]):
            La, Lb = self.L(a), self.L(b)
            steps.append("HLm_eq_wit hinj %s %s\n    %s\n    %s\n    (by decide) (by decide)"
                         % (La, Lb, self.dws(a, b), self.dws(b, a)))
        proof = steps[0]
        for st in steps[1:]:
            proof = "(%s).trans\n  (%s)" % (proof, st)
        nm = "i%d" % len(self.id_order)
        self.id_text.append("theorem %s {Γ : Finset (ℤ × ℤ)} (hinj : Inj Γ) :\n    HLm Γ %d %s = HLm Γ %d %s :=\n  %s\n"
                            % (nm, self.m, self.L(lst), self.m, self.L(R), proof))
        self.id_order.append(nm)
        res = ('id', nm)
        self.ids[lst] = res
        return res

    def atom(self, lst):
        """the lean atom (a string) for HLm Γ m lst after rewriting, or None for 0."""
        r = self.identity(lst)
        if r[0] in ('nil', 'zero'):
            return None
        key = self.closure_key(lst)
        return "HLm Γ %d %s" % (self.m, self.L(self.rep(key)))

    def rewrites(self, lsts, pr=""):
        """rw list turning HLm Γ m L_lst into the representative atoms (identity lemma names applied); with pr = "'"
        the same for HLm (mirror Γ) m L_lst (hypotheses hΓ', hinj')."""
        out = []
        seen = set()
        for lst in lsts:
            lst = tuple(lst)
            if lst in seen:
                continue
            seen.add(lst)
            r = self.identity(lst)
            if r[0] == 'id':
                out.append("%s hinj%s" % (r[1], pr))
            elif r[0] == 'zero':
                out.append("%s hΓ%s hinj%s" % (r[1], pr, pr))
            elif r[0] == 'nil':
                out.append("HLm_nil (m := %d) hΓ%s" % (self.m, pr))
        return out


# ----------------------------------------------------------------------------------------------------------------
# rows

def fr_lean(x):
    x = Fr(x)
    if x.denominator == 1:
        return "(%d : ℝ)" % x.numerator
    return "((%d : ℝ) / %d)" % (x.numerator, x.denominator)


def expr_text(terms):
    """terms: dict atom-string -> Fraction; returns a Lean real expression."""
    parts = []
    for a, c in terms.items():
        if c == 0:
            continue
        parts.append("%s * %s" % (fr_lean(c), a))
    return " + ".join(parts) if parts else "0"


MATUS_SUBSETS = None   # filled from the Lean definitions below


def matus_expansion(fam, sw, k):
    """coefficients over subsets of Fin 5 of Kleinwaks' matusL / compL (h S) with parameter k (an int)."""
    kk = Fr(k) * (k - 1) / 2
    co = {}

    def add(S, c):
        S = tuple(sorted(S))
        co[S] = co.get(S, Fr(0)) + c
    if fam == 'M':
        base = [((0,), -1), ((0, 1), 1), ((0, 4), 1), ((0, 1, 4), -1)]
        if sw:
            mid = [((0,), -1), ((1,), -1), ((2,), -1), ((4,), -1), ((0, 1), 2), ((0, 2), 1), ((0, 3), 1), ((0, 4), 1),
                   ((1, 2), 1), ((1, 3), -1), ((1, 4), 2), ((2, 3), 1), ((0, 1, 2), -1), ((0, 1, 4), -2), ((0, 2, 3), -1)]
        else:
            mid = [((0,), -1), ((1,), -2), ((4,), -1), ((0, 1), 2), ((0, 2), 1), ((0, 3), 1), ((0, 4), 1), ((1, 2), 1),
                   ((1, 3), 1), ((1, 4), 2), ((2, 3), -1), ((0, 1, 2), -1), ((0, 1, 3), -1), ((0, 1, 4), -2)]
        last = [((1,), -1), ((2,), -1), ((0, 1), 1), ((0, 2), 1), ((1, 2), 2), ((0, 1, 2), -2)]
    else:
        base = [((4,), -1), ((0, 4), 1), ((1, 4), 1), ((0, 1, 4), -1)]
        if sw:
            mid = [((0,), -2), ((1,), -1), ((2,), -1), ((0, 1), 3), ((0, 2), 1), ((0, 3), 1), ((0, 4), 1), ((1, 2), 1),
                   ((1, 3), -1), ((1, 4), 1), ((2, 3), 1), ((0, 1, 2), -1), ((0, 1, 4), -2), ((0, 2, 3), -1)]
        else:
            mid = [((0,), -2), ((1,), -2), ((0, 1), 3), ((0, 2), 1), ((0, 3), 1), ((0, 4), 1), ((1, 2), 1), ((1, 3), 1),
                   ((1, 4), 1), ((2, 3), -1), ((0, 1, 2), -1), ((0, 1, 3), -1), ((0, 1, 4), -2)]
        last = [((0,), -1), ((1,), -1), ((0, 1), 2), ((0, 2), 1), ((1, 2), 1), ((0, 1, 2), -2)]
    for S, c in base:
        add(S, Fr(c))
    for S, c in mid:
        add(S, Fr(k) * c)
    for S, c in last:
        add(S, kk * c)
    return {S: c for S, c in co.items() if c != 0}


def copy_map(cfg, U, img, transpose):
    """The map of iid copies behind a pmerge row (img = tau, transpose False) or an xshare row (img = map from copy-1
    coordinates to copy-0 coordinates, transpose True: the reflection mirF first moves the x-part of every copy to its
    y-part and back).  Each touched certificate coordinate c is realised on the lean coordinates cfg.coordmap[c] (one
    x or y of a D vertex's copy; a + b fresh copies for a W vertex of law (a, b)); its x-parts (after the reflection)
    are sent in order to the x-parts of img(c), its y-parts to the y-parts.  Returns {source copy: target copy}; the
    caller completes it to a permutation and checks that it transports the forms exactly."""
    fwd = {}
    for c in U:
        src = [(k, (1 - comp) if transpose else comp) for (k, comp) in cfg.coordmap[c]]
        dst = list(cfg.coordmap[img(c)])
        for comp in (0, 1):
            ks = [k for (k, cc) in src if cc == comp]
            kt = [k for (k, cc) in dst if cc == comp]
            assert len(ks) == len(kt), ("law types differ", c, img(c))
            for k1, k2 in zip(ks, kt):
                assert fwd.get(k1, k2) == k2, ("copy map not well defined", c)
                fwd[k1] = k2
    assert len(set(fwd.values())) == len(fwd), "copy map not injective"
    return fwd


def complete_perm(fwd, m):
    """extend an injective partial map of range(m) to a permutation; returns (fw, bw)."""
    fwd = dict(fwd)
    free_t = [k for k in range(m) if k not in set(fwd.values())]
    for k in range(m):
        if k not in fwd:
            fwd[k] = free_t.pop(0)
    fw = [fwd[k] for k in range(m)]
    assert sorted(fw) == list(range(m))
    bw = [0] * m
    for k1, k2 in enumerate(fw):
        bw[k2] = k1
    return fw, bw


def run(cert_path, name, rows_per_file, ids_per_file):
    C = json.load(open(cert_path))
    assert check3.check(cert_path), "check3.py rejects the certificate"
    E = Exporter(C, name)
    cfg = E.cfg
    m = E.m
    lam = Fr(C['claimed_lambda'])
    M = int(C['grid_depth'])
    vec = check3.vec

    rows_out = []        # (lemma name, statement, proof, copy, mult, is_ineq, lean-atom dict)
    final_terms = {}     # global atom -> Fraction coefficient (copy-qualified), to verify the identity

    def add_final(term_dict, cp, mult):
        for a, c in term_dict.items():
            key = (cp, a) if a.startswith("HLm") else a
            final_terms[key] = final_terms.get(key, Fr(0)) + mult * c

    def grid_atom(i, j, cp):
        # lean atom of h(i, j) for the copy's own grid (copy 1: transposed onto copy 0's grid)
        return "hg Γ %d %d" % ((i, j) if cp == 0 else (j, i))

    row_cache = {}       # statement -> lemma name (rows are generic in Γ, so copies share lemmas)

    def emit(stmt_terms, eq, proof, cp, mult, grid_global=False, final_override=None):
        """stmt_terms: dict atom -> coeff for the generic lemma (atoms in terms of Γ).  final_override: list of
        (copy, atom dict) for rows whose statement mixes HLm Γ and HLm (mirror Γ) (instantiated at Γ)."""
        rel = "=" if eq else "≤"
        body = expr_text(stmt_terms)
        stmt = ("%s = 0" % body) if eq else ("0 ≤ %s" % body)
        if stmt in row_cache:
            nm = row_cache[stmt]
        else:
            nm = "row%d" % len(row_cache)
            row_cache[stmt] = nm
            rows_out.append((nm, stmt, proof))
        uses.append((nm, cp, mult, eq, grid_global))
        if final_override is not None:
            for cpo, tdo in final_override:
                add_final(tdo, cpo, mult)
            return
        # final bookkeeping: map generic atoms to copy-qualified atoms
        td = {}
        for a, c in stmt_terms.items():
            if a.startswith("hg Γ"):
                _, _, i, j = a.split()
                td[grid_atom(int(i), int(j), 0 if grid_global else cp)] = td.get(
                    grid_atom(int(i), int(j), 0 if grid_global else cp), Fr(0)) + c
            else:
                td[a] = td.get(a, Fr(0)) + c
        add_final(td, cp, mult)

    uses = []
    for row in C['rows']:
        t = row['type']
        mult = Fr(row['mult'])
        cp = int(row.get('copy', 0))
        if t in ('sub', 'mono'):
            K = [cfg.lean_form(vec(g)) for g in row['K']]
            fi = cfg.lean_form(vec(row['i']))
            if t == 'sub':
                fj = cfg.lean_form(vec(row['j']))
                LA, LB, LC, LD = (fi,) + tuple(K), tuple(K) + (fj,), (fi,) + tuple(K) + (fj,), tuple(K)
                terms = {}
                for lst, c in ((LA, 1), (LB, 1), (LC, -1), (LD, -1)):
                    a = E.atom(lst)
                    if a is not None:
                        terms[a] = terms.get(a, Fr(0)) + c
                rw = E.rewrites([LC, LA, LB, LD])
                proof = ("  have h := HLm_submod hΓ [%s] %s [%s]\n"
                         "  rw [show [%s] ++ %s ++ [%s] = %s from rfl, show [%s] ++ %s = %s from rfl,\n"
                         "    show %s ++ [%s] = %s from rfl] at h\n"
                         % (E.F(fi), E.L(LD), E.F(fj), E.F(fi), E.L(LD), E.F(fj), E.L(LC), E.F(fi), E.L(LD), E.L(LA),
                            E.L(LD), E.F(fj), E.L(LB)))
            else:
                LA, LD = tuple(K) + (fi,), tuple(K)
                terms = {}
                for lst, c in ((LA, 1), (LD, -1)):
                    a = E.atom(lst)
                    if a is not None:
                        terms[a] = terms.get(a, Fr(0)) + c
                rw = E.rewrites([LA, LD])
                proof = ("  have h := HLm_mono Γ %s [%s]\n"
                         "  rw [show %s ++ [%s] = %s from rfl] at h\n" % (E.L(LD), E.F(fi), E.L(LD), E.F(fi), E.L(LA)))
            if rw:
                proof += "  rw [%s] at h\n" % ", ".join(rw)
            proof += "  linarith\n"
            emit(terms, False, proof, cp, mult)
        elif t == 'ci':
            new = sorted(int(c) for c in row['new'])
            old = sorted(int(c) for c in row['old'])
            k = cfg.vcoords.index(new)
            assert cfg.vtypes[k] in ('D', 'W')
            assert old == sorted(c for vc in cfg.vcoords[:k] for c in vc)
            lold = tuple(cfg.lean_form(check3.unitv(c)) for c in old)
            lnew = tuple(cfg.lean_form(check3.unitv(c)) for c in new)
            A = sorted({kk for c in old for (kk, _) in cfg.coordmap[c]})
            lall = lold + lnew
            terms = {}
            for lst, c in ((lall, 1), (lold, -1), (lnew, -1)):
                a = E.atom(lst)
                if a is not None:
                    terms[a] = terms.get(a, Fr(0)) + c
            rw = E.rewrites([lall, lold, lnew])
            proof = ("  have h := HLm_indepB hΓ (l₁ := %s) (l₂ := %s) [%s] (by decide) (by decide)\n"
                     "  rw [show %s ++ %s = %s from rfl] at h\n"
                     % (E.L(lold), E.L(lnew), ", ".join(str(a) for a in A), E.L(lold), E.L(lnew), E.L(lall)))
            if rw:
                proof += "  rw [%s] at h\n" % ", ".join(rw)
            proof += "  linarith\n"
            emit(terms, True, proof, cp, mult)
        elif t == 'merge':
            perm = {c: c for c in range(cfg.N)}
            perm.update({int(a): int(b) for a, b in row['perm']})
            # vertex permutation on lean vertices
            fw = list(range(m))
            for tt, (x, y) in enumerate(cfg.dv):
                tgt = cfg.dv.index((perm[x], perm[y]))
                fw[tt] = tgt
            for (w, a, b) in cfg.wv:
                w2 = perm[w]
                for k1, k2 in zip(cfg.wfresh[w], cfg.wfresh[w2]):
                    fw[k1] = k2
            assert sorted(fw) == list(range(m))
            bw = [0] * m
            for k1, k2 in enumerate(fw):
                bw[k2] = k1
            G = [vec(g) for g in row['G']]
            tG = []
            for g in G:
                h = [Fr(0)] * cfg.N
                for c in range(cfg.N):
                    h[perm[c]] += g[c]
                tG.append(h)
            LG = tuple(cfg.lean_form(g) for g in G)
            LT = tuple(cfg.lean_form(g) for g in tG)
            # check: permT bw applied to LG equals LT
            for f, f2 in zip(LG, LT):
                assert tuple(f[bw[k]] for k in range(m)) == f2
            terms = {}
            for lst, c in ((LT, 1), (LG, -1)):
                a = E.atom(lst)
                if a is not None:
                    terms[a] = terms.get(a, Fr(0)) + c
            rw = E.rewrites([LT, LG])
            fws = "![" + ", ".join(str(x) for x in fw) + "]"
            bws = "![" + ", ".join(str(x) for x in bw) + "]"
            proof = ("  have h := HLm_permB (Γ := Γ) %s %s (by decide) %s %s (by decide)\n" % (fws, bws, E.L(LG), E.L(LT)))
            if rw:
                proof += "  rw [%s] at h\n" % ", ".join(rw)
            proof += "  linarith\n"
            emit(terms, True, proof, cp, mult)
        elif t == 'rshare':
            # H_0(cl phi(G)) = H_1(cl G): copy 1 = the reflected coupling; HLm (mirror Γ) m LG = HLm Γ m (LG.map mirF)
            # (HLm_mirror), then a permutation of the copies moves each reflected W_a onto W_b (wmap, transposed law)
            G = [vec(g) for g in row['G']]
            wm = {int(a): int(b) for a, b in row.get('wmap', [])}
            pG = []
            for g in G:
                h = [Fr(0)] * cfg.N
                for (x, y) in cfg.dv:
                    h[x], h[y] = -g[y], -g[x]
                for a, b in wm.items():
                    h[b] -= g[a]
                pG.append(h)
            fwd = {k: k for k in range(cfg.nD)}
            wlaw = {w: (a, b) for (w, a, b) in cfg.wv}
            for a, b in wm.items():
                ia, ja = wlaw[a]
                assert wlaw[b] == (ja, ia)
                fa, fb = cfg.wfresh[a], cfg.wfresh[b]
                for r in range(ia):            # x-copies of W_a (carry -y after mirF) -> y-copies of W_b
                    fwd[fa[r]] = fb[ja + r]
                for s_ in range(ja):           # y-copies of W_a (carry -x after mirF) -> x-copies of W_b
                    fwd[fa[ia + s_]] = fb[s_]
            assert len(set(fwd.values())) == len(fwd)
            free_t = [k for k in range(m) if k not in set(fwd.values())]
            for k in range(m):
                if k not in fwd:
                    fwd[k] = free_t.pop(0)
            fw = [fwd[k] for k in range(m)]
            bw = [0] * m
            for k1, k2 in enumerate(fw):
                bw[k2] = k1
            LG = tuple(cfg.lean_form(g) for g in G)
            LP = tuple(cfg.lean_form(g) for g in pG)
            LT = tuple(tuple((-f[bw[k]][1], -f[bw[k]][0]) for k in range(m)) for f in LG)
            assert LT == LP, ("rshare transport", LT, LP)
            a0 = E.atom(LP)
            a1 = E.atom(LG)
            terms = {}
            if a0 is not None:
                terms[a0] = Fr(1)
            if a1 is not None:
                terms[a1.replace("HLm Γ ", "HLm (mirror Γ) ", 1)] = Fr(-1)
            fin = [(0, {a0: Fr(1)} if a0 is not None else {}), (1, {a1: Fr(-1)} if a1 is not None else {})]
            fws = "![" + ", ".join(str(x) for x in fw) + "]"
            bws = "![" + ", ".join(str(x) for x in bw) + "]"
            proof = ("  have hΓ' := mirror_nonempty hΓ\n  have hinj' := mirror_inj hinj\n"
                     "  have h := HLm_mirror_permB Γ %s %s (by decide) %s %s (by decide)\n" % (fws, bws, E.L(LG), E.L(LP)))
            rw1 = E.rewrites([LG], "'")
            rw0 = E.rewrites([LP])
            if rw1 + rw0:
                proof += "  rw [%s] at h\n" % ", ".join(rw1 + rw0)
            proof += "  linarith\n"
            emit(terms, True, proof, 0, mult, True, final_override=fin)
        elif t == 'pmerge':
            # H(cl tau G) = H(cl G), tau a coordinate permutation sending the touched part of each vertex into one
            # vertex with the same marginal law, distinct vertices to distinct vertices (check3): a permutation of the
            # iid copies (HLm_permB), generic in the copy's Γ
            perm = {c: c for c in range(cfg.N)}
            perm.update({int(a): int(b) for a, b in row['perm']})
            assert sorted(perm.values()) == list(range(cfg.N))
            G = [vec(g) for g in row['G']]
            U = sorted({c for g in G for c in range(cfg.N) if g[c] != 0})
            fw, bw = complete_perm(copy_map(cfg, U, lambda c: perm[c], False), m)
            tG = []
            for g in G:
                h = [Fr(0)] * cfg.N
                for c in range(cfg.N):
                    h[perm[c]] += g[c]
                tG.append(h)
            LG = tuple(cfg.lean_form(g) for g in G)
            LT = tuple(cfg.lean_form(g) for g in tG)
            for f, f2 in zip(LG, LT):
                assert tuple(f[bw[k]] for k in range(m)) == f2, ("pmerge transport", f, f2)
            terms = {}
            for lst, c in ((LT, 1), (LG, -1)):
                a = E.atom(lst)
                if a is not None:
                    terms[a] = terms.get(a, Fr(0)) + c
            rw = E.rewrites([LT, LG])
            fws = "![" + ", ".join(str(x) for x in fw) + "]"
            bws = "![" + ", ".join(str(x) for x in bw) + "]"
            proof = ("  have h := HLm_permB (Γ := Γ) %s %s (by decide) %s %s (by decide)\n" % (fws, bws, E.L(LG), E.L(LT)))
            if rw:
                proof += "  rw [%s] at h\n" % ", ".join(rw)
            proof += "  linarith\n"
            emit(terms, True, proof, cp, mult)
        elif t == 'xshare':
            # H_0(cl tau G) = H_1(cl G), (tau g)_{map(c)} = -g_c: copy 1 (the reflected coupling) is realised on copy 0's
            # space by the reflection mirF (HLm_mirror), then a permutation of the copies (HLm_mirror_permB)
            mp = {int(a): int(b) for a, b in row['map']}
            G = [vec(g) for g in row['G']]
            U = sorted({c for g in G for c in range(cfg.N) if g[c] != 0})
            assert sorted(mp) == U, "map must be defined exactly on the support"
            pG = []
            for g in G:
                h = [Fr(0)] * cfg.N
                for c in U:
                    h[mp[c]] -= g[c]
                pG.append(h)
            fw, bw = complete_perm(copy_map(cfg, U, lambda c: mp[c], True), m)
            LG = tuple(cfg.lean_form(g) for g in G)
            LP = tuple(cfg.lean_form(g) for g in pG)
            LT = tuple(tuple((-f[bw[k]][1], -f[bw[k]][0]) for k in range(m)) for f in LG)
            assert LT == LP, ("xshare transport", LT, LP)
            a0 = E.atom(LP)
            a1 = E.atom(LG)
            terms = {}
            if a0 is not None:
                terms[a0] = Fr(1)
            if a1 is not None:
                terms[a1.replace("HLm Γ ", "HLm (mirror Γ) ", 1)] = Fr(-1)
            fin = [(0, {a0: Fr(1)} if a0 is not None else {}), (1, {a1: Fr(-1)} if a1 is not None else {})]
            fws = "![" + ", ".join(str(x) for x in fw) + "]"
            bws = "![" + ", ".join(str(x) for x in bw) + "]"
            proof = ("  have hΓ' := mirror_nonempty hΓ\n  have hinj' := mirror_inj hinj\n"
                     "  have h := HLm_mirror_permB Γ %s %s (by decide) %s %s (by decide)\n" % (fws, bws, E.L(LG), E.L(LP)))
            rw1 = E.rewrites([LG], "'")
            rw0 = E.rewrites([LP])
            if rw1 + rw0:
                proof += "  rw [%s] at h\n" % ", ".join(rw1 + rw0)
            proof += "  linarith\n"
            emit(terms, True, proof, 0, mult, True, final_override=fin)
        elif t == 'dpair':
            v = int(row['vertex'])
            x, y = cfg.dv[v]
            lst = (cfg.lean_form(check3.unitv(x)), cfg.lean_form(check3.unitv(y)))
            a = E.atom(lst)
            terms = {"Real.log #Γ": Fr(1)}
            terms[a] = terms.get(a, Fr(0)) - 1
            rw = E.rewrites([lst])
            proof = "  have h := HLm_pairKB hΓ %d %s (by decide)\n" % (v, E.L(lst))
            if rw:
                proof += "  rw [%s] at h\n" % ", ".join(rw)
            proof += "  linarith\n"
            emit(terms, True, proof, cp, mult)
        elif t == 'bsum':
            f = vec(row['f'])
            lf = cfg.lean_form(f)
            # f = +-(x + y): x an X-valued coordinate, y a Y-valued one (lean: x of some copy, y of some copy)
            nz = [(k, comp, val) for k, p in enumerate(lf) for comp, val in enumerate(p) if val != 0]
            assert len(nz) == 2, ("bsum form", lf)
            xs = [z for z in nz if z[1] == 0]
            ys = [z for z in nz if z[1] == 1]
            assert len(xs) == 1 and len(ys) == 1 and xs[0][2] == ys[0][2] and abs(xs[0][2]) == 1, ("bsum form", lf)
            sgn = xs[0][2]
            base = tuple(((1 if (k == xs[0][0]) else 0), (1 if (k == ys[0][0]) else 0)) for k in range(m))
            # (a copy may carry both coordinates: x_a + y_a)
            base = tuple((1 if k == xs[0][0] else 0, 1 if k == ys[0][0] else 0) for k in range(m))
            a = E.atom((lf,))
            terms = {"Real.log #(X + Y)": Fr(1)}
            terms[a] = terms.get(a, Fr(0)) - 1
            proof = "  have h := HLm_bsumB hΓ hXY %s %d %d (by decide)\n" % (E.F(base), xs[0][0], ys[0][0])
            lb = (base,)
            if sgn == 1:
                rw = E.rewrites([lb])
                proof += "  rw [show [%s] = %s from rfl] at h\n" % (E.F(base), E.L(lb))
            else:
                rw = E.rewrites([lb])
                proof += "  rw [show [%s] = %s from rfl] at h\n" % (E.F(base), E.L(lb))
                # [lf] and [base] have the same closure, so both rewrite to the same representative
                assert E.closure_key((lf,)) == E.closure_key(lb)
            if rw:
                proof += "  rw [%s] at h\n" % ", ".join(rw)
            proof += "  linarith\n"
            emit(terms, False, proof, cp, mult)
        elif t == 'ident':
            f = vec(row['f'])
            ij = check3.grid_form(f)
            assert ij is not None and list(ij) == [int(x) for x in row['ij']]
            i, j = ij
            assert 0 <= i <= M and 0 <= j <= M
            lf = cfg.lean_form(f)
            # lean counts agree with check3's (W of law (1,0) is one fresh x)
            ci = sum(1 for p in lf if p == (1, 0))
            cj = sum(1 for p in lf if p == (0, 1))
            assert (ci, cj) == (i, j), (lf, ij)
            a = E.atom((lf,))
            terms = {"hg Γ %d %d" % (i, j): Fr(1)}
            terms[a] = terms.get(a, Fr(0)) - 1
            rw = E.rewrites([(lf,)])
            proof = ("  have h := HLm_gridB hΓ %s %d %d (by decide)\n"
                     "  rw [show [%s] = %s from rfl] at h\n" % (E.F(lf), i, j, E.F(lf), E.L((lf,))))
            if rw:
                proof += "  rw [%s] at h\n" % ", ".join(rw)
            proof += "  unfold hg\n  linarith\n"
            emit(terms, True, proof, cp, mult)
        elif t.startswith('g_'):
            ij = row['ij']
            if t == 'g_h00':
                emit({"hg Γ 0 0": Fr(-1)}, True, "  have h := hg_h00 (Γ := Γ)\n  linarith\n", 0, mult, True)
            elif t == 'g_h11':
                emit({"Real.log #(X + Y)": Fr(1), "hg Γ 1 1": Fr(-1)}, False,
                     "  have h := hg_h11 hΓ hXY\n  linarith\n", 0, mult, True)
            else:
                i, j = int(ij[0]), int(ij[1])
                if t == 'g_nonneg':
                    terms = {"hg Γ %d %d" % (i, j): Fr(1)}
                    pf = "  have h := hg_nonneg hΓ %d %d\n  linarith\n" % (i, j)
                elif t == 'g_monox':
                    terms = {"hg Γ %d %d" % (i + 1, j): Fr(1), "hg Γ %d %d" % (i, j): Fr(-1)}
                    pf = "  have h := hg_monox hΓ %d %d\n  linarith\n" % (i, j)
                elif t == 'g_monoy':
                    terms = {"hg Γ %d %d" % (i, j + 1): Fr(1), "hg Γ %d %d" % (i, j): Fr(-1)}
                    pf = "  have h := hg_monoy hΓ %d %d\n  linarith\n" % (i, j)
                elif t == 'g_concx':
                    terms = {"hg Γ %d %d" % (i + 1, j): Fr(2), "hg Γ %d %d" % (i, j): Fr(-1),
                             "hg Γ %d %d" % (i + 2, j): Fr(-1)}
                    pf = "  have h := hg_concx hΓ %d %d\n  linarith\n" % (i, j)
                elif t == 'g_concy':
                    terms = {"hg Γ %d %d" % (i, j + 1): Fr(2), "hg Γ %d %d" % (i, j): Fr(-1),
                             "hg Γ %d %d" % (i, j + 2): Fr(-1)}
                    pf = "  have h := hg_concy hΓ %d %d\n  linarith\n" % (i, j)
                elif t == 'g_link':
                    terms = {"hg Γ %d %d" % (i + 1, j): Fr(1), "hg Γ %d %d" % (i, j + 1): Fr(1),
                             "hg Γ %d %d" % (i, j): Fr(-1), "Real.log #Γ": Fr(-1)}
                    pf = "  have h := hg_link hΓ hinj %d %d\n  linarith\n" % (i, j)
                else:
                    raise ValueError(t)
                emit(terms, False, pf, 0, mult, True)
        elif t in ('matus4', 'five'):
            V = [tuple(cfg.lean_form(vec(g)) for g in gl) for gl in row['vars']]
            if t == 'matus4':
                fam, k = 'M', int(row['s'])
                vs = V + [V[2]]
                cand = [(fam, sw) for sw in (False, True)]
            else:
                fam, k = row['fam'], int(row['k'])
                vs = V
                cand = [(fam, sw) for sw in (False, True)]
            # check3's expression for this row, keyed by closure
            R3 = {}

            def Hj(idx):
                lst = ()
                for q in idx:
                    lst = lst + V[q]
                return lst
            # rebuild check3's R via its own code path on lean lists
            a_, b_, c_, d_ = 0, 1, 2, 3

            def I(w, p, q, r=None):
                if r is None:
                    for idx, cc in (((p,), w), ((q,), w), ((p, q), -w)):
                        R3[E.closure_key(Hj(idx))] = R3.get(E.closure_key(Hj(idx)), Fr(0)) + cc
                else:
                    for idx, cc in (((p, r), w), ((q, r), w), ((p, q, r), -w), ((r,), -w)):
                        R3[E.closure_key(Hj(idx))] = R3.get(E.closure_key(Hj(idx)), Fr(0)) + cc

            def ingleton(w, x, y, z, u):
                I(-w, x, y); I(w, x, y, z); I(w, x, y, u); I(w, z, u)
            if t == 'matus4':
                s = k
                I(1, b_, c_, a_)
                ingleton(s, a_, b_, c_, d_)
                I(s * (s + 1) // 2, a_, c_, b_)
                I(s * (s + 1) // 2, a_, b_, c_)
            else:
                z = 4
                if row['variant'] == 'abcd':
                    ingleton(k, a_, b_, c_, d_)
                else:
                    ingleton(k, a_, c_, b_, d_)
                kk = k * (k - 1) // 2
                if row['fam'] == 'M':
                    I(1, b_, z, a_); I(k, a_, z, b_); I(k, a_, b_, z); I(kk, a_, c_, b_); I(kk, a_, b_, c_)
                else:
                    I(1, a_, b_, z); I(k, a_, z, b_); I(k, b_, z, a_); I(kk, a_, c_, b_); I(kk, b_, c_, a_)
            R3 = {kk_: cc for kk_, cc in R3.items() if cc != 0 and kk_}
            chosen = None
            for fam_, sw in cand:
                ex = matus_expansion(fam_, sw, k)
                RL = {}
                for S, cc in ex.items():
                    lst = ()
                    for q in S:
                        lst = lst + vs[q]
                    key = E.closure_key(lst)
                    if key:
                        RL[key] = RL.get(key, Fr(0)) + cc
                RL = {kk_: cc for kk_, cc in RL.items() if cc != 0}
                if RL == R3:
                    chosen = (fam_, sw, ex)
                    break
            assert chosen is not None, ("non-Shannon row does not match a Lean family", row)
            fam_, sw, ex = chosen
            terms = {}
            haves = []
            Vnames = [E.L(v) for v in vs]
            vsl = "![%s]" % ", ".join(Vnames)
            for S, cc in ex.items():
                lst = ()
                for q in S:
                    lst = lst + vs[q]
                a = E.atom(lst)
                if a is not None:
                    terms[a] = terms.get(a, Fr(0)) + cc
                fs = "{" + ", ".join(str(q) for q in S) + "}"
                ls = "[" + ", ".join(str(q) for q in S) + "]"
                rw = E.rewrites([lst])
                Ln = E.L(lst)
                hv = ("  have hS%s : HS (Om Γ %d) (wt Γ %d) (jv %s) %s = %s := by\n"
                      "    rw [show (%s : Finset (Fin 5)) = (%s : List (Fin 5)).toFinset from by decide,\n"
                      "      HS_jv Γ %s %s (by decide), show (%s : List (Fin 5)).flatMap %s = %s from rfl]\n"
                      % ("_".join(str(q) for q in S), m, m, vsl, fs,
                         (a if a is not None else "0"), fs, ls, vsl, ls, ls, vsl, Ln))
                if rw:
                    hv += "    rw [%s]\n" % ", ".join(rw)
                haves.append(hv)
            lemma = "matus_ineq" if fam_ == 'M' else "companion_ineq"
            Ldef = "matusL" if fam_ == 'M' else "compL"
            swt = "true" if sw else "false"
            proof = ("  have hM := %s (G := List ℤ) %d %s (Om Γ %d) (wt Γ %d) (wt_nonneg Γ %d) (wt_sum hΓ %d)\n"
                     "    (jv %s)\n  simp only [%s, %s] at hM\n"
                     % (lemma, k, swt, m, m, m, m, vsl, Ldef,
                        "↓reduceIte" if sw else "Bool.false_eq_true, ↓reduceIte"))
            proof += "".join(haves)
            proof += "  norm_num at hM\n  linarith [%s]\n" % ", ".join(
                ["hM"] + ["hS%s" % "_".join(str(q) for q in S) for S in ex])
            emit(terms, False, proof, cp, mult)
        else:
            raise ValueError("row type %r not supported yet" % t)

    # ---- verify the final identity exactly
    target = {"Real.log #(X + Y)": lam, "Real.log #Γ": Fr(-1)}
    resid = {}
    for a, c in final_terms.items():
        tgt = target.get(a, Fr(0))
        if c != tgt:
            resid[a] = (c, tgt)
    for a in target:
        if a not in final_terms and target[a] != 0:
            resid[a] = (Fr(0), target[a])
    if resid:
        print("FAIL: final identity does not hold in the Lean atoms; %d residual atoms" % len(resid))
        for a, v in list(resid.items())[:10]:
            print("  ", a, v)
        sys.exit(1)
    print("identity OK: %d rows -> %d row lemmas, %d identity lemmas, %d lists, %d forms, m = %d"
          % (len(uses), len(rows_out), len(E.id_order), len(E.lists), len(E.forms), m))
    write_files(E, name, lam, rows_out, uses, rows_per_file, ids_per_file, cert_path)


HEADER_COMMON = """set_option linter.unusedVariables false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
"""


def write_files(E, name, lam, rows_out, uses, rows_per_file, ids_per_file, cert_path):
    m = E.m
    base = os.path.join(ROOT, "EntropyBounds", "TwoSet", "Certs", name)
    os.makedirs(base, exist_ok=True)
    ns = "EntropyBounds.TwoSet.Certs.%s" % name
    mod = "EntropyBounds.TwoSet.Certs.%s" % name
    certname = os.path.basename(cert_path)
    certsha = hashlib.sha256(open(cert_path, "rb").read()).hexdigest()
    chksha = hashlib.sha256(open(check3.__file__, "rb").read()).hexdigest()
    # Defs
    lines = ["import EntropyBounds.Iid.Witness\n",
             "/-! Forms and lists of the certificate `%s` (sha256 %s; generated by tools/export_twoset_x.py). -/\n"
             % (certname, certsha),
             "namespace %s\n" % ns, "open EntropyBounds.Iid\n",
             "/-- Distinct differences in `Γ`. -/",
             "abbrev Inj (Γ : Finset (ℤ × ℤ)) : Prop := ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q'\n"]
    for f in E.form_order:
        lines.append("def %s : Form %d := ![%s]" % (E.forms[f], m, ", ".join("(%d, %d)" % p for p in f)))
    lines.append("")
    for lst in E.list_order:
        lines.append("def %s : List (Form %d) := [%s]" % (E.lists[lst], m, ", ".join(E.forms[f] for f in lst)))
    lines.append("\nend %s\n" % ns)
    open(os.path.join(base, "Defs.lean"), "w").write("\n".join(lines))
    # Ids
    nid = len(E.id_text)
    id_files = []
    for s in range(0, max(nid, 1), ids_per_file):
        fn = "Ids%d" % (s // ids_per_file)
        id_files.append(fn)
        txt = ["import %s.Defs\n" % mod, HEADER_COMMON, "namespace %s\n" % ns, "open EntropyBounds.Iid\n"]
        txt += E.id_text[s:s + ids_per_file]
        txt.append("end %s\n" % ns)
        open(os.path.join(base, fn + ".lean"), "w").write("\n".join(txt))
    # Rows
    row_files = []
    imports_ids = "".join("import %s.%s\n" % (mod, f) for f in id_files)
    for s in range(0, len(rows_out), rows_per_file):
        fn = "Rows%d" % (s // rows_per_file)
        row_files.append(fn)
        txt = [imports_ids + "import EntropyBounds.Iid.NonShannon\nimport EntropyBounds.TwoSet.Common\n"
               + ("import EntropyBounds.TwoSet.Mirror\n" if any("HLm_mirror" in pf for (_, _, pf) in rows_out) else ""),
               HEADER_COMMON, "open Finset Pointwise\n", "namespace %s\n" % ns,
               "open SumsDifferences SumsDifferences.NonShannon EntropyBounds.Iid EntropyBounds.TwoSet"
               + (" SumsDifferences.CoupledForms" if any("HLm_mirror" in pf for (_, _, pf) in rows_out) else "")
               + "\n"]
        for (nm, stmt, proof) in rows_out[s:s + rows_per_file]:
            txt.append("theorem %s (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)\n"
                       "    (hXY : Γ ⊆ X ×ˢ Y) :\n    %s := by\n%s" % (nm, stmt, proof))
        txt.append("end %s\n" % ns)
        open(os.path.join(base, fn + ".lean"), "w").write("\n".join(txt))
    # Final
    lam_s = "(%d / %d : ℝ)" % (lam.numerator, lam.denominator)
    two = 2 - 1 / lam
    txt = ["".join("import %s.%s\n" % (mod, f) for f in row_files),
           HEADER_COMMON, "open Finset Pointwise\n",
           "/-!\n# The two-set exponent certificate `%s`, checked in Lean\n\n"
           "Certificate file `%s`, sha256 `%s`; rows re-derived by check3.py, sha256 `%s`\n"
           "(tools/ref/check3_8ab8e59a.py).\n\n"
           "`pair_ceiling`: `|X − Y| ≤ |X + Y|^λ` for all finite `X, Y ⊆ ℤ`, `λ = %s`; `theta_le` (Kleinwaks' θ, every K)\n"
           "and `thetaK_le` (Tao's page 3a / GGSTW 6.44: fixed implied constants): `C_3a ≤ 2 − 1/λ = %s`.\n-/\n"
           % (certname, certname, certsha, chksha, lam, two),
           "namespace %s\n" % ns,
           "open SumsDifferences EntropyBounds.Iid EntropyBounds.TwoSet SumsDifferences.CoupledForms\n"]
    hs = []
    body = []
    stmt_of = {nm: stmt for (nm, stmt, proof) in rows_out}
    for idx, (nm, cp, mult, eq, gg) in enumerate(uses):
        hn = "h%d" % idx
        if cp == 0 or gg:
            body.append("  have %s := %s Γ X Y hΓ hinj hXY" % (hn, nm))
        else:
            body.append("  have %s := %s (mirror Γ) (-Y) (-X) hΓ' hinj' hXY'" % (hn, nm))
            st = stmt_of[nm]
            lem = []
            if "Real.log #Γ" in st:
                lem.append("log_card_mirror")
            if "Real.log #(X + Y)" in st:
                lem.append("log_card_negsum")
            if "hg Γ" in st:
                lem.append("hg_mirror")
            if lem:
                body.append("  simp only [%s] at %s" % (", ".join(lem), hn))
        # linear_combination reads `c * h` for `h : e = 0` as `c * e` on the LEFT of the combined inequality and for
        # `h : 0 ≤ e` as `c * e` on the RIGHT, so equality rows enter with the opposite sign
        hs.append((hn, -mult if eq else mult))
    comb = " + ".join("%s * %s" % (fr_lean(mu), hn) for hn, mu in hs if mu != 0)
    # large certificates (more than 3000 row uses): a higher heartbeat limit for the final linear_combination (the
    # earlier certificates have at most 2292 uses, so their generated files are unchanged)
    txt.append(("set_option maxHeartbeats 40000000 in\n" if len(uses) > 3000 else "") +
               "theorem cert_ineq (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)\n"
               "    (hXY : Γ ⊆ X ×ˢ Y) : Real.log #Γ ≤ %s * Real.log #(X + Y) := by\n"
               "  have hΓ' := mirror_nonempty hΓ\n  have hinj' := mirror_inj hinj\n  have hXY' := mirror_subset hXY\n"
               % lam_s + "\n".join(body) + "\n  linear_combination %s\n" % comb)
    txt.append("theorem pair_ceiling (X Y : Finset ℤ) : (#(X - Y) : ℝ) ≤ (#(X + Y) : ℝ) ^ %s :=\n"
               "  pair_ceiling_of_cert (by norm_num) (fun Γ X Y hΓ hinj hXY => cert_ineq Γ X Y hΓ hinj hXY) X Y\n"
               % lam_s)
    txt.append("theorem theta_le : theta ≤ (%d / %d : ℝ) := by\n"
               "  have h := theta_le_of_pair_ceiling pair_ceiling\n  norm_num at h ⊢\n  linarith\n"
               % (two.numerator, two.denominator))
    txt.append("theorem thetaK_le : thetaK ≤ (%d / %d : ℝ) := by\n"
               "  have h := thetaK_le_of_pair_ceiling pair_ceiling\n  norm_num at h ⊢\n  linarith\n"
               % (two.numerator, two.denominator))
    txt.append("end %s\n" % ns)
    open(os.path.join(base, "Final.lean"), "w").write("\n".join(txt))
    # Headline: the fixed-constant bound without suprema
    hl = ["import %s.Final\nimport EntropyBounds.TwoSet.Headline\n" % mod,
          "/-!\n# `%s`: the fixed-constant bound without suprema\n\n"
          "`admissibleK_le_value`: every exponent `θ` admissible with fixed constants (`AdmissibleK θ`, Tao's page 3a /\n"
          "GGSTW 6.44) satisfies `θ ≤ %s`.  (`thetaK_le` in `Final` is the same bound for the supremum `thetaK`, and\n"
          "`one_le_thetaK` shows that this supremum is taken over a nonempty bounded set.)\n-/\n" % (certname, two),
          "namespace %s\n" % ns, "open EntropyBounds.TwoSet\n",
          "theorem admissibleK_le_value {θ : ℝ} (h : AdmissibleK θ) : θ ≤ (%d / %d : ℝ) := by\n"
          "  have h1 := admissibleK_le_of_pair_ceiling pair_ceiling h\n  norm_num at h1 ⊢\n  linarith\n"
          % (two.numerator, two.denominator),
          "end %s\n" % ns]
    open(os.path.join(base, "Headline.lean"), "w").write("\n".join(hl))
    # TorsionFree: the pair ceiling for finite subsets of torsion-free abelian groups (EntropyBounds/TwoSet/TorsionFree.lean)
    tf = ["import %s.Final\nimport EntropyBounds.TwoSet.TorsionFree\n" % mod,
          "/-!\n# `%s` in torsion-free abelian groups\n\n"
          "`pair_ceiling_torsionFree`: `|X − Y| ≤ |X + Y|^λ` for all finite subsets `X, Y` of a torsion-free abelian group,\n"
          "`λ = %s`, from `pair_ceiling` (finite subsets of `ℤ`) by `card_sub_le_of_int`.\n-/\n" % (certname, lam),
          "open Finset Pointwise\n", "namespace %s\n" % ns, "open EntropyBounds.TwoSet\n",
          "theorem pair_ceiling_torsionFree {G : Type*} [AddCommGroup G] [IsAddTorsionFree G] [DecidableEq G]\n"
          "    (X Y : Finset G) : (#(X - Y) : ℝ) ≤ (#(X + Y) : ℝ) ^ %s :=\n"
          "  card_sub_le_of_int pair_ceiling X Y\n" % lam_s,
          "end %s\n" % ns]
    open(os.path.join(base, "TorsionFree.lean"), "w").write("\n".join(tf))
    print("wrote %s: Defs, %d Ids files, %d Rows files, Final, Headline, TorsionFree" % (base, len(id_files), len(row_files)))


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("cert")
    ap.add_argument("name")
    ap.add_argument("--rows-per-file", type=int, default=150)
    ap.add_argument("--ids-per-file", type=int, default=200)
    a = ap.parse_args()
    run(a.cert, a.name, a.rows_per_file, a.ids_per_file)
