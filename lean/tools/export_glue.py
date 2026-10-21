#!/usr/bin/env python3
"""Export a sum-difference entropy certificate (check630.py format) as Lean modules.

Usage: python3 -I tools/export_glue.py CERT.json NAME [--rows-per-file N] [--ids-per-file N]

Writes EntropyBounds/Glue/Certs/NAME/{Defs,Glue,Ids_k,Rows_k,Final}.lean.  The certificate is untrusted data: it is
first checked by check630.py (snapshot tools/ref/check630.py), then every ingredient becomes a Lean lemma proved
from EntropyBounds/Glue:

* the glued configuration: `C0 = base Γ p` (the law `p` of the pair on its support `Γ`), and one `Conf.copy` per
  copy step of the certificate; every relation that check630 derives for a step is proved in Lean
  (`Conf.rel_copy_new`, with a determination of the relation's form from the step's key `V` by explicit witnesses);
* closure classes in the final configuration: one representative list each, identity lemmas with determination
  witnesses modulo the relations (checked by `decide`);
* one lemma per row (Shannon `sub`/`mono`, `ci` and `eqlaw` of a copy step, `matus` via Kleinwaks' `matus_ineq`);
  the `eqlaw` classes of the certificate become equality rows whose multipliers are found here (spanning trees);
* the final `linear_combination`, then `entropy_ineq` (the entropy form for pairs with injective difference) and
  `set_ineq` (Tao's page 3b set form, via `set_form`).
"""
import sys, os, json, math, io, argparse, contextlib
from fractions import Fraction as Fr

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "ref"))
import check630  # noqa: E402  (read-only snapshot)
sys.path.insert(0, HERE)
import export_lemmas  # noqa: E402

ROOT = os.path.dirname(HERE)
D = (1, -1)


# ----------------------------------------------------------------------------------------------------------------
# exact linear algebra on flat vectors (length 2N: x_v at 2v, y_v at 2v + 1)

def express(target, vecs):
    """Rational coefficients mu with sum mu_i vecs_i = target, or None."""
    n = len(vecs)
    rows = []
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


def fr_lean(x):
    x = Fr(x)
    if x.denominator == 1:
        return "(%d : ℝ)" % x.numerator
    return "((%d : ℝ) / %d)" % (x.numerator, x.denominator)


def expr_text(terms):
    parts = ["%s * %s" % (fr_lean(c), a) for a, c in terms.items() if c != 0]
    return " + ".join(parts) if parts else "0"


MATUS = None


def matus_expansion(fam, sw, k):
    """coefficients over subsets of Fin 5 of Kleinwaks' matusL / compL (h S) with parameter k."""
    kk = Fr(k) * (k - 1) / 2
    co = {}

    def add(S, c):
        S = tuple(sorted(S))
        co[S] = co.get(S, Fr(0)) + c
    base = [((0,), -1), ((0, 1), 1), ((0, 4), 1), ((0, 1, 4), -1)]
    if sw:
        mid = [((0,), -1), ((1,), -1), ((2,), -1), ((4,), -1), ((0, 1), 2), ((0, 2), 1), ((0, 3), 1), ((0, 4), 1),
               ((1, 2), 1), ((1, 3), -1), ((1, 4), 2), ((2, 3), 1), ((0, 1, 2), -1), ((0, 1, 4), -2), ((0, 2, 3), -1)]
    else:
        mid = [((0,), -1), ((1,), -2), ((4,), -1), ((0, 1), 2), ((0, 2), 1), ((0, 3), 1), ((0, 4), 1), ((1, 2), 1),
               ((1, 3), 1), ((1, 4), 2), ((2, 3), -1), ((0, 1, 2), -1), ((0, 1, 3), -1), ((0, 1, 4), -2)]
    last = [((1,), -1), ((2,), -1), ((0, 1), 1), ((0, 2), 1), ((1, 2), 2), ((0, 1, 2), -2)]
    assert fam == 'M'
    for S, c in base:
        add(S, Fr(c))
    for S, c in mid:
        add(S, Fr(k) * c)
    for S, c in last:
        add(S, kk * c)
    return {S: c for S, c in co.items() if c != 0}


HEADER = """set_option linter.unusedVariables false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
"""


class Space:
    """closure, representatives and witnesses for one configuration (relations R, vertices < nv)."""

    def __init__(self, N, R, nv):
        self.N, self.R, self.nv = N, [list(map(Fr, r)) for r in R], nv
        self.Rrows = check630.rref(self.R) if self.R else []

    def unit(self, k, c):
        v = [Fr(0)] * (2 * self.N)
        v[2 * k + c] = Fr(1)
        return v

    def dvec(self, k):
        v = [Fr(0)] * (2 * self.N)
        v[2 * k] = Fr(1)
        v[2 * k + 1] = Fr(-1)
        return v

    def rounds(self, S):
        S = [list(map(Fr, f)) for f in S]
        out = [list(S)]
        while True:
            span = S + self.R
            new = [k for k in range(self.nv) if in_span(self.dvec(k), span)
                   and not (in_span(self.unit(k, 0), span) and in_span(self.unit(k, 1), span))]
            if not new:
                break
            for k in new:
                S = S + [self.unit(k, 0), self.unit(k, 1)]
            out.append(list(S))
        return out

    def key(self, S):
        last = self.rounds(S)[-1]
        rows = sorted(check630.rref(last + self.R))      # rref keeps insertion order: sort by pivot
        return tuple(tuple(r) for p, r in rows)

    def rep(self, key):
        """canonical integer basis of the closure modulo the relations."""
        out = []
        for r in key:
            v = check630.reduce_vec(list(r), self.Rrows)
            if any(a != 0 for a in v):
                out.append(tuple(primitive(v)))
        return tuple(out)

    def dwr(self, S, f):
        """one-round witness for f from S modulo R (tuples of ints), or None."""
        Sv = [list(map(Fr, x)) for x in S]
        f = list(map(Fr, f))
        gens = [k for k in range(self.nv) if in_span(self.dvec(k), Sv + self.R)]
        aug = Sv + self.R + [self.unit(k, c) for k in gens for c in (0, 1)]
        mu = express(f, aug)
        if mu is None:
            return None
        c = lcm_den(mu)
        nS, nR = len(Sv), len(self.R)
        ms = [int(x * c) for x in mu[:nS]]
        rs = [int(x * c) for x in mu[nS:nS + nR]]
        g = [[0, 0] for _ in range(self.N)]
        for idx, k in enumerate(gens):
            g[k][0] = int(mu[nS + nR + 2 * idx] * c)
            g[k][1] = int(mu[nS + nR + 2 * idx + 1] * c)
        wc = [1] * self.N
        wit = [[] for _ in range(self.N)]
        wr = [[] for _ in range(self.N)]
        for k in range(self.N):
            if g[k] != [0, 0]:
                nu = express(self.dvec(k), Sv + self.R)
                d = lcm_den(nu)
                wc[k] = d
                wit[k] = [int(x * d) for x in nu[:nS]]
                wr[k] = [int(x * d) for x in nu[nS:]]
        return (c, ms, rs, g, wc, wit, wr)


def dwr_text(w):
    c, ms, rs, g, wc, wit, wr = w
    lst = lambda xs: "[" + ", ".join(str(x) for x in xs) + "]"
    return "⟨%d, %s, %s, ![%s], ![%s], ![%s], ![%s]⟩" % (
        c, lst(ms), lst(rs), ", ".join("(%d, %d)" % tuple(p) for p in g), ", ".join(str(x) for x in wc),
        ", ".join(lst(x) for x in wit), ", ".join(lst(x) for x in wr))


class Exporter:
    def __init__(self, C, name):
        self.C, self.name = C, name
        self.slopes = [tuple(s) for s in C['slopes']]
        assert sorted(self.slopes) == [(0, 1), (1, 0), (1, 1)], "only C_3b slopes {(1,0),(0,1),(1,1)} supported"
        self.SL = self.slopes + [D]
        self.forms, self.form_order = {}, []
        self.lists, self.list_order = {}, []
        # replay the steps with check630's own code, recording alphas
        conf = check630.Conf(C['slopes'])
        self.steps = []
        for st in C['steps']:
            assert 'link' not in st, "link steps are not supported yet"
            U = list(st['U'])
            V = [(int(v), tuple(s)) for v, s in st['V']]
            n_before = conf.n
            rel_before = [list(r) for r in conf.rel]
            Vg = [('std', v, s) for v, s in V]
            cl = conf.closure(Vg)
            Z = [list(x) for x in cl] + [conf.pad(r) for r in conf.rel]
            keep = set(2 * u + c for u in U for c in (0, 1))
            alphas = check630.sub_coord_space(Z, keep, 2 * conf.n)
            nrel = len(conf.rel)
            conf.attach(U, V)
            newids = conf.steps[-1][3]
            added = conf.rel[nrel:]
            assert len(added) == len(alphas)
            self.steps.append(dict(U=U, V=V, newids=newids, n_before=n_before, rel_before=rel_before,
                                   alphas=[list(a) for a in alphas]))
        self.N = conf.n
        self.conf = conf
        N = self.N
        pad = lambda v: [Fr(x) for x in v] + [Fr(0)] * (2 * N - len(v))
        # integer relations per configuration: R_t = relations of C_t
        self.R = [[]]
        for t, st in enumerate(self.steps):
            src = [None] * N
            for k, u in enumerate(st['U']):
                src[st['newids'][k]] = u
            st['src'] = src
            news = []
            for a in st['alphas']:
                ai = primitive(pad(a))
                b = [0] * (2 * N)
                for k, u in enumerate(st['U']):
                    for c in (0, 1):
                        b[2 * st['newids'][k] + c] += ai[2 * u + c]
                r = [b[i] - ai[i] for i in range(2 * N)]
                news.append((tuple(b), tuple(ai), tuple(r)))
            st['news'] = news
            self.R.append(self.R[-1] + [n[2] for n in news])
        # check: the integer relations span check630's final relation space
        Rf = check630.rref([pad(r) for r in conf.rel])
        Ri = check630.rref([list(map(Fr, r)) for r in self.R[-1]])
        assert [tuple(r) for p, r in Rf] == [tuple(r) for p, r in Ri], "relation spaces differ"
        self.extra = [tuple(int(x) for x in f) for f in C.get('extra', [])]
        for f in self.extra:
            assert len(f) == 2 * N
        self.final = Space(N, self.R[-1], N)
        self.rep_of_key = {}
        self.ids, self.id_order, self.id_text = {}, [], []

    # --- forms and lists
    def std(self, v, s):
        f = [0] * (2 * self.N)
        f[2 * v], f[2 * v + 1] = s
        return tuple(f)

    def ref(self, g):
        if g[0] == 'amb':
            return self.extra[int(g[1])]
        return self.std(int(g[0]), (int(g[1][0]), int(g[1][1])))

    def F(self, f):
        f = tuple(int(x) for x in f)
        if f not in self.forms:
            self.forms[f] = "F%d" % len(self.forms)
            self.form_order.append(f)
        return self.forms[f]

    def L(self, lst):
        lst = tuple(tuple(int(x) for x in f) for f in lst)
        if not lst:
            return "([] : List (Form %d))" % self.N
        for f in lst:
            self.F(f)
        if lst not in self.lists:
            self.lists[lst] = "L%d" % len(self.lists)
            self.list_order.append(lst)
        return self.lists[lst]

    def form_lean(self, f):
        return "![" + ", ".join("(%d, %d)" % (f[2 * k], f[2 * k + 1]) for k in range(self.N)) + "]"

    # --- closure classes in the final configuration
    def rep(self, key):
        if key not in self.rep_of_key:
            self.rep_of_key[key] = self.final.rep(key)
        return self.rep_of_key[key]

    def dws(self, sp, S, T):
        out = []
        for f in T:
            w = sp.dwr(S, f)
            assert w is not None, "form not determined in one round"
            out.append(dwr_text(w))
        return "[" + ", ".join(out) + "]"

    def identity(self, lst):
        lst = tuple(tuple(int(x) for x in f) for f in lst)
        if lst in self.ids:
            return self.ids[lst]
        sp = self.final
        key = sp.key(lst)
        R = self.rep(key)
        if not R:
            if not lst:
                res = ('nil',)
            else:
                nm = "z%d" % len(self.id_order)
                Ln = self.L(lst)
                self.id_text.append(
                    "theorem %s {Γ : Finset (ℝ × ℝ)} {p : ℝ × ℝ → ℝ} (h : Hyp Γ p) : (CF Γ p).H %s = 0 :=\n"
                    "  Conf.H_eq_zero_wit h.inj (hvF h) (relF h) %s %s (by decide)\n"
                    % (nm, Ln, Ln, self.dws(sp, (), lst)))
                self.id_order.append(nm)
                res = ('zero', nm)
            self.ids[lst] = res
            return res
        self.L(R)
        if R == lst:
            res = ('rep',)
            self.ids[lst] = res
            return res
        rs = sp.rounds(lst)
        chain = [lst]
        for S in rs[1:]:
            chain.append(tuple(tuple(int(x) for x in v) for v in S))
        chain.append(R)
        steps = []
        for a, b in zip(chain[:-1], chain[1:]):
            steps.append("Conf.H_eq_wit h.inj (hvF h) (relF h) %s %s\n    %s\n    %s\n    (by decide) (by decide)"
                         % (self.L(a), self.L(b), self.dws(sp, a, b), self.dws(sp, b, a)))
        proof = steps[0]
        for st in steps[1:]:
            proof = "(%s).trans\n  (%s)" % (proof, st)
        nm = "i%d" % len(self.id_order)
        self.id_text.append("theorem %s {Γ : Finset (ℝ × ℝ)} {p : ℝ × ℝ → ℝ} (h : Hyp Γ p) :\n"
                            "    (CF Γ p).H %s = (CF Γ p).H %s :=\n  %s\n" % (nm, self.L(lst), self.L(R), proof))
        self.id_order.append(nm)
        res = ('id', nm)
        self.ids[lst] = res
        return res

    def atom(self, lst):
        r = self.identity(lst)
        if r[0] in ('nil', 'zero'):
            return None
        return "(CF Γ p).H %s" % self.L(self.rep(self.final.key(lst)))

    def akey(self, lst):
        """the closure key of an atom (None for the zero atom)."""
        k = self.final.key(lst)
        return k if self.rep(k) else None

    def rewrites(self, lsts):
        out, seen = [], set()
        for lst in lsts:
            lst = tuple(tuple(int(x) for x in f) for f in lst)
            if lst in seen:
                continue
            seen.add(lst)
            r = self.identity(lst)
            if r[0] == 'id':
                out.append("%s h" % r[1])
            elif r[0] == 'zero':
                out.append("%s h" % r[1])
            elif r[0] == 'nil':
                out.append("Conf.H_nil (hvF h).nonneg (hvF h).sum_one")
        return out


def run(cert_path, name, rows_per_file, ids_per_file):
    C = json.load(open(cert_path))
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        try:
            Ctot = check630.main(cert_path)
        except SystemExit as e:
            print(buf.getvalue())
            raise SystemExit("check630.py rejects the certificate (%s)" % e)
    print(buf.getvalue().strip())
    E = Exporter(C, name)
    N = E.N
    T = len(E.steps)
    LEM = None
    if C.get('lemmas'):
        LEM = export_lemmas.build(C)      # (NL, infos, order, texts); check630.verify_lemma runs on every lemma
    lam = {tuple(int(x) for x in k.split(',')): Fr(v) for k, v in C['lambda'].items()}
    uses = []            # (lemma name, mult, is_eq)
    rows_out = []        # (lemma name, statement, proof)
    row_cache = {}
    final_terms = {}     # closure key -> coefficient (rows only)

    def emit(terms, keys, eq, proof, mult):
        stmt = ("%s = 0" % expr_text(terms)) if eq else ("0 ≤ %s" % expr_text(terms))
        if stmt in row_cache:
            nm = row_cache[stmt]
        else:
            nm = "row%d" % len(row_cache)
            row_cache[stmt] = nm
            rows_out.append((nm, stmt, proof))
        uses.append((nm, mult, eq))
        for k, c in keys.items():
            final_terms[k] = final_terms.get(k, Fr(0)) + mult * c

    def add_atom(terms, keys, lst, c):
        a = E.atom(lst)
        if a is None:
            return
        terms[a] = terms.get(a, Fr(0)) + c
        k = E.akey(lst)
        keys[k] = keys.get(k, Fr(0)) + c

    def lift_text(lists, t1):
        """rewrites (CF).H l -> (C_t1).H l for lists using only vertices that exist in C_t1."""
        out = []
        seen = set()
        for lst in lists:
            Ln = E.L(lst)
            if Ln in seen or not lst:
                continue
            seen.add(Ln)
            if t1 < T:
                out.append("lift%d h %s %s" % (t1, Ln, " ".join(["(by decide)"] * (T - t1))))
        return out

    std_old = lambda n: [E.std(v, s) for v in range(n) for s in E.SL]
    # ---- rows
    for row in C['rows']:
        t = row['type']
        mult = Fr(row['mult'])
        if t in ('sub', 'mono'):
            K = [E.ref(g) for g in row['K']]
            fi = E.ref(row['i'])
            terms, keys = {}, {}
            if t == 'sub':
                fj = E.ref(row['j'])
                LA, LB, LC, LD = [fi] + K, K + [fj], [fi] + K + [fj], K
                for lst, c in ((LA, 1), (LB, 1), (LC, -1), (LD, -1)):
                    add_atom(terms, keys, lst, c)
                rw = E.rewrites([LC, LA, LB, LD])
                proof = ("  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [%s] %s [%s]\n"
                         "  rw [show [%s] ++ %s ++ [%s] = %s from rfl, show [%s] ++ %s = %s from rfl,\n"
                         "    show %s ++ [%s] = %s from rfl] at hh\n"
                         % (E.F(fi), E.L(LD), E.F(fj), E.F(fi), E.L(LD), E.F(fj), E.L(LC), E.F(fi), E.L(LD), E.L(LA),
                            E.L(LD), E.F(fj), E.L(LB)))
            else:
                LA, LD = K + [fi], K
                for lst, c in ((LA, 1), (LD, -1)):
                    add_atom(terms, keys, lst, c)
                rw = E.rewrites([LA, LD])
                proof = ("  have hh := Conf.H_mono (hvF h).nonneg %s [%s]\n"
                         "  rw [show %s ++ [%s] = %s from rfl] at hh\n" % (E.L(LD), E.F(fi), E.L(LD), E.F(fi), E.L(LA)))
            if rw:
                proof += "  rw [%s] at hh\n" % ", ".join(rw)
            proof += "  linarith\n"
            emit(terms, keys, False, proof, mult)
        elif t == 'ci':
            st_i = int(row['step'])
            st = E.steps[st_i]
            n0 = st['n_before']
            Lold = std_old(n0)
            B = [E.std(v, s) for v in st['newids'] for s in E.SL]
            A = [E.std(st['src'][v], s) for v in st['newids'] for s in E.SL]
            Vf = [E.std(v, s) for v, s in st['V']]
            L1, L2, L3, L4 = Lold + B + Vf, Vf, Lold + Vf, B + Vf
            terms, keys = {}, {}
            # check630: + cl(V + new) + cl(old) - cl(old + new) - cl(V)
            for lst, c in ((L4, 1), (L3, 1), (L1, -1), (L2, -1)):
                add_atom(terms, keys, lst, c)
            t1 = st_i + 1
            lifts = lift_text([L1, L2, L3, L4], t1)
            cn = "CF" if t1 == T else "C%d" % t1
            proof = ("  have hh : (%s Γ p).H (%s ++ %s ++ %s) + (%s Γ p).H %s = (%s Γ p).H (%s ++ %s) + (%s Γ p).H (%s ++ %s) :=\n"
                     "    Conf.H_copy_ci (src := src%d) (V := V%d) (hv%d h) (by decide) %s %s %s (by decide) (by decide) (by decide)\n"
                     "      (by decide)\n"
                     % (cn, E.L(Lold), E.L(B), E.L(Vf), cn, E.L(Vf), cn, E.L(Lold), E.L(Vf), cn, E.L(B), E.L(Vf),
                        st_i, st_i, st_i, E.L(Lold), E.L(B), E.L(A)))
            proof += ("  rw [show %s ++ %s ++ %s = %s from rfl, show %s ++ %s = %s from rfl, show %s ++ %s = %s from rfl] at hh\n"
                      % (E.L(Lold), E.L(B), E.L(Vf), E.L(L1), E.L(Lold), E.L(Vf), E.L(L3), E.L(B), E.L(Vf), E.L(L4)))
            if lifts:
                proof += "  rw [%s] at hh\n" % ", ".join("← " + x for x in lifts)
            rw = E.rewrites([L1, L2, L3, L4])
            if rw:
                proof += "  rw [%s] at hh\n" % ", ".join(rw)
            proof += "  linarith\n"
            emit(terms, keys, True, proof, mult)
        elif t == 'matus':
            k = int(row['s'])
            V5 = [[E.ref(g) for g in row[x]] for x in ('a', 'b', 'c', 'd')]
            vs = V5 + [V5[2]]
            R3 = {}

            def Hj(idx):
                lst = []
                for q in idx:
                    lst = lst + V5[q]
                return lst

            def Iq(w, x, y, z):
                for idx, cc in ((x + z, w), (y + z, w), (x + y + z, -w), (z, -w)):
                    kk = E.akey(Hj(idx))
                    if kk is not None:
                        R3[kk] = R3.get(kk, Fr(0)) + cc
            a_, b_, c_, d_ = [0], [1], [2], [3]
            cc_ = Fr(k * (k + 1), 2)
            Iq(Fr(1), b_, c_, a_)
            Iq(Fr(-k), a_, b_, [])
            Iq(Fr(k), a_, b_, c_)
            Iq(Fr(k), a_, b_, d_)
            Iq(Fr(k), c_, d_, [])
            Iq(cc_, a_, c_, b_)
            Iq(cc_, a_, b_, c_)
            R3 = {kk: cc for kk, cc in R3.items() if cc != 0}
            chosen = None
            for sw in (False, True):
                ex = matus_expansion('M', sw, k)
                RL = {}
                for S, cc in ex.items():
                    lst = []
                    for q in S:
                        lst = lst + vs[q]
                    kk = E.akey(lst)
                    if kk is not None:
                        RL[kk] = RL.get(kk, Fr(0)) + cc
                RL = {kk: cc for kk, cc in RL.items() if cc != 0}
                if RL == R3:
                    chosen = (sw, ex)
                    break
            assert chosen is not None, ("matus row does not match a Lean instance", row)
            sw, ex = chosen
            terms, keys = {}, {}
            haves = []
            vsl = "![%s]" % ", ".join(E.L(v) for v in vs)
            for S, cc in ex.items():
                lst = []
                for q in S:
                    lst = lst + vs[q]
                add_atom(terms, keys, lst, cc)
                a = E.atom(lst)
                fs = "{" + ", ".join(str(q) for q in S) + "}"
                ls = "[" + ", ".join(str(q) for q in S) + "]"
                rw = E.rewrites([lst])
                hv = ("  have hS%s : HS (CF Γ p).Ω (CF Γ p).p (jvC (CF Γ p) %s) %s = %s := by\n"
                      "    rw [show (%s : Finset (Fin 5)) = (%s : List (Fin 5)).toFinset from by decide,\n"
                      "      HS_jvC (CF Γ p) (hvF h).nonneg %s %s (by decide), show (%s : List (Fin 5)).flatMap %s = %s from rfl]\n"
                      % ("_".join(str(q) for q in S), vsl, fs, (a if a is not None else "0"), fs, ls, vsl, ls, ls, vsl,
                         E.L(lst)))
                if rw:
                    hv += "    rw [%s]\n" % ", ".join(rw)
                haves.append(hv)
            proof = ("  have hM := matus_ineq (G := List ℝ) %d %s (CF Γ p).Ω (CF Γ p).p (hvF h).nonneg (hvF h).sum_one\n"
                     "    (jvC (CF Γ p) %s)\n  simp only [matusL, %s] at hM\n"
                     % (k, "true" if sw else "false", vsl, "↓reduceIte" if sw else "Bool.false_eq_true, ↓reduceIte"))
            proof += "".join(haves)
            proof += "  norm_num at hM\n  linarith [%s]\n" % ", ".join(
                ["hM"] + ["hS%s" % "_".join(str(q) for q in S) for S in ex])
            emit(terms, keys, False, proof, mult)
        elif t == 'lemma':
            assert LEM is not None
            NL, infos = LEM[0], LEM[1]
            lid = str(row['lemma'])
            info = infos[lid]
            args = [[E.ref(g) for g in a] for a in row['args']]
            assert len(args) == len(info.base) == 4
            vs = args + [[] for _ in range(NL - 4)]
            vsl = "![%s]" % ", ".join(E.L(v) for v in vs)
            terms, keys = {}, {}
            rws, flats, lsts = [], [], []
            for S, c in sorted(info.coef.items(), key=lambda kv: sorted(kv[0])):
                if c == 0:
                    continue
                Ls = sorted(S)
                lst = []
                for q in Ls:
                    lst = lst + args[q]
                add_atom(terms, keys, lst, c)
                lsts.append(lst)
                rws.append("Conf.H_lsp (hvF h).nonneg %s [%s] (by decide) %s (by decide)"
                           % (vsl, ", ".join(str(q) for q in Ls), export_lemmas.fs(S, NL)))
                flats.append("show ([%s] : List (Fin %d)).flatMap %s = %s from rfl"
                             % (", ".join(str(q) for q in Ls), NL, vsl, E.L(lst)))
            proof = ("  have hL := lem_%s ((CF Γ p).lsp %s) (Conf.valid_lsp (hvF h) %s)\n"
                     "  rw [%s] at hL\n  rw [%s] at hL\n" % (lid, vsl, vsl, ", ".join(rws), ", ".join(flats)))
            rw = E.rewrites(lsts)
            if rw:
                proof += "  rw [%s] at hL\n" % ", ".join(rw)
            proof += "  linarith\n"
            emit(terms, keys, False, proof, mult)
        else:
            raise ValueError("row type %r not supported yet" % t)

    # ---- eqlaw equalities (free multipliers)
    eq_rows = []     # (terms, keys, proof, keyA, keyB)
    for e in C['eqlaw']:
        st_i = int(e['step'])
        st = E.steps[st_i]
        Vf = [E.std(v, s) for v, s in st['V']]
        A, B, LV = [], [], []
        for g in e['gens']:
            v, s = int(g[0]), (int(g[1][0]), int(g[1][1]))
            f = E.std(v, s)
            if (v, s) in st['V']:
                LV.append(f)
            else:
                assert v in st['U'], ("eqlaw generator", g)
                A.append(f)
                B.append(E.std(st['newids'][st['U'].index(v)], s))
        LA, LB = A + LV, B + LV
        terms, keys = {}, {}
        add_atom(terms, keys, LB, Fr(1))
        add_atom(terms, keys, LA, Fr(-1))
        t1 = st_i + 1
        lifts = lift_text([LA, LB], t1)
        cn = "CF" if t1 == T else "C%d" % t1
        proof = ("  have hh : (%s Γ p).H (%s ++ %s) = (%s Γ p).H (%s ++ %s) :=\n"
                 "    Conf.H_copy_eqlaw (src := src%d) (V := V%d) (hv%d h) (by decide) %s %s %s (by decide) (by decide)\n"
                 "      (by decide) (by decide)\n"
                 % (cn, E.L(B), E.L(LV), cn, E.L(A), E.L(LV), st_i, st_i, st_i, E.L(B), E.L(LV), E.L(A)))
        proof += ("  rw [show %s ++ %s = %s from rfl, show %s ++ %s = %s from rfl] at hh\n"
                  % (E.L(B), E.L(LV), E.L(LB), E.L(A), E.L(LV), E.L(LA)))
        if lifts:
            proof += "  rw [%s] at hh\n" % ", ".join("← " + x for x in lifts)
        rw = E.rewrites([LA, LB])
        if rw:
            proof += "  rw [%s] at hh\n" % ", ".join(rw)
        proof += "  linarith\n"
        eq_rows.append((terms, keys, proof, E.akey(LB), E.akey(LA)))

    # ---- target: lambda_s H(pi_s(g0)) - H(g0)
    g0 = [E.std(0, (1, 0)), E.std(0, (0, 1))]
    target = {}
    kg0 = E.akey(g0)
    target[kg0] = target.get(kg0, Fr(0)) - 1
    slope_lists = {}
    for s, v in lam.items():
        lst = [E.std(0, s)]
        slope_lists[s] = lst
        ks = E.akey(lst)
        target[ks] = target.get(ks, Fr(0)) + v
    # residual = target - rows; must be absorbed by the eqlaw equalities (each: +key(B) - key(A))
    resid = {k: target.get(k, Fr(0)) - final_terms.get(k, Fr(0)) for k in set(target) | set(final_terms)}
    resid = {k: c for k, c in resid.items() if c != 0 and k is not None}
    # spanning forest over eqlaw edges; solve sum_e mu_e (B_e - A_e) = resid
    adj = {}
    for idx, (_, _, _, kb, ka) in enumerate(eq_rows):
        if kb is None or ka is None or kb == ka:
            continue
        adj.setdefault(kb, []).append((ka, idx, +1))
        adj.setdefault(ka, []).append((kb, idx, -1))
    mu = [Fr(0)] * len(eq_rows)
    seen = set()
    for root in list(adj):
        if root in seen:
            continue
        # BFS tree
        order, parent = [root], {root: None}
        seen.add(root)
        qi = 0
        while qi < len(order):
            x = order[qi]
            qi += 1
            for (y, idx, sgn) in adj[x]:
                if y not in seen:
                    seen.add(y)
                    parent[y] = (x, idx, sgn)
                    order.append(y)
        need = {x: resid.get(x, Fr(0)) for x in order}
        for x in reversed(order[1:]):
            px, idx, sgn = parent[x]
            # edge idx contributes mu*(+1) at kb and mu*(-1) at ka; here x is reached from px:
            # sgn = +1: px = kb, x = ka (edge contributes -mu at x); sgn = -1: px = ka, x = kb (+mu at x)
            if sgn == +1:
                mu[idx] = -need[x]
                need[px] -= mu[idx]
            else:
                mu[idx] = need[x]
                need[px] += mu[idx]
            need[x] = Fr(0)
        assert need[root] == 0, "eqlaw class sum is not zero"
    for (terms, keys, proof, kb, ka), m_ in zip(eq_rows, mu):
        emit(terms, keys, True, proof, m_)
    # ---- verify the identity exactly: rows (incl. eqlaw) = target
    bad = {k: (final_terms.get(k, Fr(0)), target.get(k, Fr(0))) for k in set(target) | set(final_terms)
           if k is not None and final_terms.get(k, Fr(0)) != target.get(k, Fr(0))}
    if bad:
        print("FAIL: final identity does not hold in the Lean atoms; %d residual classes" % len(bad))
        sys.exit(1)
    print("identity OK: %d row uses -> %d row lemmas, %d identity lemmas, %d lists, %d forms, N = %d"
          % (len(uses), len(rows_out), len(E.id_order), len(E.lists), len(E.forms), N))
    # g0 and slope identities for the final step
    E.identity(g0)
    for s in slope_lists:
        E.identity(slope_lists[s])
    write_files(E, name, lam, rows_out, uses, rows_per_file, ids_per_file, cert_path, g0, slope_lists, Ctot, LEM)


def write_files(E, name, lam, rows_out, uses, rows_per_file, ids_per_file, cert_path, g0, slope_lists, Ctot, LEM=None):
    N = E.N
    T = len(E.steps)
    base = os.path.join(ROOT, "EntropyBounds", "Glue", "Certs", name)
    os.makedirs(base, exist_ok=True)
    mod = "EntropyBounds.Glue.Certs.%s" % name
    ns = mod
    certname = os.path.basename(cert_path)
    opens = "open EntropyBounds.Iid EntropyBounds.Glue SumsDifferences SumsDifferences.NonShannon\n"
    # ---- Glue.lean: steps, configurations, validity, relations, lifts (written before Defs so that the lists it
    # registers are defined)
    g = []
    srcs = []
    for t, st in enumerate(E.steps):
        tbl = ", ".join("none" if s is None else "some %d" % s for s in st['src'])
        g.append("/-- Step %d: copies of the vertices %s at %s over the key %s. -/\ndef src%d : Fin %d → Option (Fin %d) := ![%s]\n"
                 % (t, st['U'], st['newids'], st['V'], t, N, N, tbl))
        g.append("def V%d : List (Form %d) := %s\n" % (t, N, E.L([E.std(v, s) for v, s in st['V']])))
    g.append("/-- The glued configurations. -/\nnoncomputable abbrev C0 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) : Conf %d := base Γ p\n" % N)
    for t in range(T):
        g.append("noncomputable abbrev C%d (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) : Conf %d := (C%d Γ p).copy src%d V%d\n"
                 % (t + 1, N, t, t, t))
    g.append("noncomputable abbrev CF (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) : Conf %d := C%d Γ p\n" % (N, T))
    g.append("theorem hv0 {Γ : Finset (ℝ × ℝ)} {p : ℝ × ℝ → ℝ} (h : Hyp Γ p) : (C0 Γ p).Valid Γ :=\n"
             "  valid_base h.nonneg h.sum_one\n")
    for t in range(T):
        g.append("theorem hv%d {Γ : Finset (ℝ × ℝ)} {p : ℝ × ℝ → ℝ} (h : Hyp Γ p) : (C%d Γ p).Valid Γ :=\n"
                 "  Conf.valid_copy (hv%d h) src%d V%d\n" % (t + 1, t + 1, t, t, t))
    g.append("theorem hvF {Γ : Finset (ℝ × ℝ)} {p : ℝ × ℝ → ℝ} (h : Hyp Γ p) : (CF Γ p).Valid Γ := hv%d h\n" % T)
    # relations
    g.append("def R0 : List (Form %d) := []\n" % N)
    g.append("theorem rel0 {Γ : Finset (ℝ × ℝ)} {p : ℝ × ℝ → ℝ} (h : Hyp Γ p) : ∀ r ∈ R0, (C0 Γ p).Rel r := by\n"
             "  intro r hr; exact absurd hr List.not_mem_nil\n")
    for t, st in enumerate(E.steps):
        sp = Space(N, E.R[t], st['n_before'])
        Vf = [E.std(v, s) for v, s in st['V']]
        newnames = []
        for j, (b, a, r) in enumerate(st['news']):
            # determination of alpha from V in C_t: closure rounds, then one witness for alpha
            rs = sp.rounds(Vf)
            chain = [tuple(Vf)] + [tuple(tuple(int(x) for x in v) for v in S) for S in rs[1:]]
            lines = []
            prev = None
            for i in range(1, len(chain)):
                lines.append("  have d%d : ∀ g ∈ %s, (C%d Γ p).Det %s g :=\n"
                             "    Conf.det_of_checkDWRs h.inj (hv%d h) (rel%d h) (ws := %s) (by decide)\n"
                             % (i, E.L(chain[i]), t, E.L(chain[i - 1]), t, t, E.dws(sp, chain[i - 1], chain[i])))
            wa = sp.dwr(chain[-1], a)
            assert wa is not None
            lines.append("  have da : (C%d Γ p).Det %s %s :=\n"
                         "    Conf.det_of_checkDWR h.inj (hv%d h) (rel%d h) (w := %s) (by decide)\n"
                         % (t, E.L(chain[-1]), E.F(a), t, t, dwr_text(wa)))
            # compose: chain[0] = V
            if len(chain) == 1:
                lines.append("  have dV : (C%d Γ p).Det V%d %s := da\n" % (t, t, E.F(a)))
            else:
                # e_i : forall g in chain[i], Det chain[0] g
                lines.append("  have e1 : ∀ g ∈ %s, (C%d Γ p).Det V%d g := d1\n" % (E.L(chain[1]), t, t))
                for i in range(2, len(chain)):
                    lines.append("  have e%d : ∀ g ∈ %s, (C%d Γ p).Det V%d g := fun g hg => Conf.Det.trans e%d (d%d g hg)\n"
                                 % (i, E.L(chain[i]), t, t, i - 1, i))
                lines.append("  have dV : (C%d Γ p).Det V%d %s := Conf.Det.trans e%d da\n" % (t, t, E.F(a), len(chain) - 1))
            nm = "newrel%d_%d" % (t, j)
            newnames.append((nm, r))
            g.append("theorem %s {Γ : Finset (ℝ × ℝ)} {p : ℝ × ℝ → ℝ} (h : Hyp Γ p) : (C%d Γ p).Rel %s := by\n"
                     % (nm, t + 1, E.F(r)) + "".join(lines) +
                     "  exact Conf.rel_copy_new (src := src%d) (V := V%d) (by decide) (b := %s) (α := %s) (by decide) (by decide)\n"
                     "    (by decide) dV (by decide)\n" % (t, t, E.F(b), E.F(a)))
        newlist = "[" + ", ".join(E.F(r) for _, r in newnames) + "]"
        g.append("def R%d : List (Form %d) := R%d ++ %s\n" % (t + 1, N, t, newlist))
        cases = "\n".join("    · exact %s h" % nm for nm, _ in newnames)
        if newnames:
            second = ("  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr\n"
                      "    rcases hr with %s\n%s\n" % (" | ".join(["rfl"] * len(newnames)), cases))
        else:
            second = "  · exact absurd hr List.not_mem_nil\n"
        g.append("theorem rel%d {Γ : Finset (ℝ × ℝ)} {p : ℝ × ℝ → ℝ} (h : Hyp Γ p) : ∀ r ∈ R%d, (C%d Γ p).Rel r := by\n"
                 "  intro r hr\n"
                 "  rcases List.mem_append.mp hr with hr | hr\n"
                 "  · exact Conf.rel_copy_old (rel%d h r hr) (List.all_eq_true.mp (show R%d.all (oldF src%d) = true by decide) r hr)\n"
                 % (t + 1, t + 1, t + 1, t, t, t) + second)
    g.append("def RF : List (Form %d) := R%d\n" % (N, T))
    g.append("theorem relF {Γ : Finset (ℝ × ℝ)} {p : ℝ × ℝ → ℝ} (h : Hyp Γ p) : ∀ r ∈ RF, (CF Γ p).Rel r := rel%d h\n" % T)
    # lifts: (CF).H l = (C_k).H l for lists old for steps k..T-1
    for k in range(1, T):
        hyps = " ".join("(h%d : l.all (oldF src%d) = true)" % (j, j) for j in range(k, T))
        chain = " ".join("rw [Conf.H_copy_old (hv%d h) l h%d]" % (j, j) for j in reversed(range(k, T)))
        body = "\n".join("  rw [show (C%d Γ p).H l = (C%d Γ p).H l from Conf.H_copy_old (hv%d h) l h%d]" % (j + 1, j, j, j)
                         for j in reversed(range(k, T)))
        g.append("theorem lift%d {Γ : Finset (ℝ × ℝ)} {p : ℝ × ℝ → ℝ} (h : Hyp Γ p) (l : List (Form %d)) %s :\n"
                 "    (CF Γ p).H l = (C%d Γ p).H l := by\n  show (C%d Γ p).H l = _\n%s\n" % (k, N, hyps, k, T, body))
    hyps0 = " ".join("(h%d : l.all (oldF src%d) = true)" % (j, j) for j in range(0, T))
    body0 = "\n".join("  rw [show (C%d Γ p).H l = (C%d Γ p).H l from Conf.H_copy_old (hv%d h) l h%d]" % (j + 1, j, j, j)
                      for j in reversed(range(0, T)))
    g.append("theorem lift0 {Γ : Finset (ℝ × ℝ)} {p : ℝ × ℝ → ℝ} (h : Hyp Γ p) (l : List (Form %d)) %s :\n"
             "    (CF Γ p).H l = (C0 Γ p).H l := by\n  show (C%d Γ p).H l = _\n%s\n" % (N, hyps0, T, body0))
    # ---- identity lemmas need all lists registered: they are (rows were emitted before)
    # ---- Defs.lean
    lines = ["import EntropyBounds.Glue.SetForm\n",
             "/-! Forms and lists of the certificate `%s` (generated by tools/export_glue.py). -/\n" % certname,
             "namespace %s\n" % ns, opens]
    lines.append("abbrev Inj (Γ : Finset (ℝ × ℝ)) : Prop := ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q'\n")
    for f in E.form_order:
        lines.append("def %s : Form %d := %s" % (E.forms[f], N, E.form_lean(f)))
    for lst in E.list_order:
        lines.append("def %s : List (Form %d) := [%s]" % (E.lists[lst], N, ", ".join(E.forms[f] for f in lst)))
    lines.append("\nend %s\n" % ns)
    open(os.path.join(base, "Defs.lean"), "w").write("\n".join(lines))
    gl = ["import %s.Defs\n" % mod, HEADER, "open Finset\n",
          "/-! The glued configuration of `%s`: copy steps, validity, relations (proved), lifts. -/\n" % certname,
          "namespace %s\n" % ns, opens] + g + ["end %s\n" % ns]
    open(os.path.join(base, "Glue.lean"), "w").write("\n".join(gl))
    # Ids
    nid = len(E.id_text)
    id_files = []
    for s in range(0, max(nid, 1), ids_per_file):
        fn = "Ids%d" % (s // ids_per_file)
        id_files.append(fn)
        txt = ["import %s.Glue\n" % mod, HEADER, "namespace %s\n" % ns, opens]
        txt += E.id_text[s:s + ids_per_file]
        txt.append("end %s\n" % ns)
        open(os.path.join(base, fn + ".lean"), "w").write("\n".join(txt))
    imports_ids = "".join("import %s.%s\n" % (mod, f) for f in id_files)
    if LEM is not None:
        NL, infos, order, texts = LEM
        lt = ["import EntropyBounds.Lemma.Basic\n", HEADER,
              "/-! The lemmas of `%s` (generated by tools/export_lemmas.py): each is proved from its copy steps. -/\n"
              % certname, "namespace %s\n" % ns, "open EntropyBounds.Lem\n"] + texts + ["end %s\n" % ns]
        open(os.path.join(base, "Lemmas.lean"), "w").write("\n".join(lt))
        imports_ids += "import %s.Lemmas\nimport EntropyBounds.Glue.Lemma\n" % mod
    row_files = []
    for s in range(0, len(rows_out), rows_per_file):
        fn = "Rows%d" % (s // rows_per_file)
        row_files.append(fn)
        txt = [imports_ids, HEADER, "open Finset\n", "namespace %s\n" % ns, opens + ("open EntropyBounds.Lem\n" if LEM is not None else "")]
        for (nm, stmt, proof) in rows_out[s:s + rows_per_file]:
            txt.append("theorem %s (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :\n    %s := by\n%s"
                       % (nm, stmt, proof))
        txt.append("end %s\n" % ns)
        open(os.path.join(base, fn + ".lean"), "w").write("\n".join(txt))
    # Final
    l10, l01, l11 = lam[(1, 0)], lam[(0, 1)], lam[(1, 1)]
    hs, body = [], []
    for idx, (nm, mult, eq) in enumerate(uses):
        hn = "h%d" % idx
        body.append("  have %s := %s Γ p h" % (hn, nm))
        hs.append((hn, -mult if eq else mult))
    comb = " + ".join("%s * %s" % (fr_lean(mu), hn) for hn, mu in hs if mu != 0)
    rep_of = lambda lst: E.L(E.rep(E.final.key(lst)))
    rwg = E.rewrites([g0] + [slope_lists[s] for s in ((1, 0), (0, 1), (1, 1))])
    gx, gy, gs = slope_lists[(1, 0)], slope_lists[(0, 1)], slope_lists[(1, 1)]
    txt = ["".join("import %s.%s\n" % (mod, f) for f in row_files), HEADER, "open Finset\n",
           "/-!\n# The sum-difference certificate `%s`, checked in Lean\n\n"
           "`entropy_ineq`: `H(X, Y) ≤ %s H(X) + %s H(Y) + %s H(X + Y)` for every finitely supported pair of real random\n"
           "variables with `x − y` injective on the support; `set_ineq`: for finite `A, B ⊆ ℝ` and `G ⊆ A × B`,\n"
           "`|A −_G B| ≤ max(|A|, |B|, |A +_G B|)^C`, `C = %s` (Tao's page 3b, `C_3b`).\n-/\n"
           % (certname, l10, l01, l11, Ctot),
           "namespace %s\n" % ns, opens]
    lam_s = lambda x: "(%d / %d : ℝ)" % (x.numerator, x.denominator)
    txt.append("theorem cf_ineq (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :\n"
               "    (CF Γ p).H %s ≤ %s * (CF Γ p).H %s + %s * (CF Γ p).H %s + %s * (CF Γ p).H %s := by\n"
               % (E.L(g0), lam_s(l10), E.L(gx), lam_s(l01), E.L(gy), lam_s(l11), E.L(gs))
               + ("  rw [%s]\n" % ", ".join(rwg) if rwg else "")
               + "\n".join(body) + "\n  linear_combination %s\n" % comb)
    txt.append("theorem entropy_ineq (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (hinj : Inj Γ) (hp : ∀ q ∈ Γ, 0 ≤ p q)\n"
               "    (hs : ∑ q ∈ Γ, p q = 1) :\n"
               "    pushEntropy Γ p (fun q => q) ≤ %s * pushEntropy Γ p (fun q => q.1) + %s * pushEntropy Γ p (fun q => q.2)\n"
               "      + %s * pushEntropy Γ p (fun q => q.1 + q.2) := by\n"
               "  have h : Hyp Γ p := ⟨hinj, hp, hs⟩\n"
               "  have key := cf_ineq Γ p h\n"
               "  rw [lift0 h %s %s, lift0 h %s %s, lift0 h %s %s, lift0 h %s %s] at key\n"
               "  rw [show %s = [%s, %s] from rfl, H_base_pairB hp %s %s 0 (by decide) (by decide),\n"
               "    show %s = [%s] from rfl, H_base_xB hp %s 0 (by decide),\n"
               "    show %s = [%s] from rfl, H_base_yB hp %s 0 (by decide),\n"
               "    show %s = [%s] from rfl, H_base_sumB hp %s 0 (by decide)] at key\n"
               "  exact key\n"
               % (lam_s(l10), lam_s(l01), lam_s(l11),
                  E.L(g0), " ".join(["(by decide)"] * T), E.L(gx), " ".join(["(by decide)"] * T),
                  E.L(gy), " ".join(["(by decide)"] * T), E.L(gs), " ".join(["(by decide)"] * T),
                  E.L(g0), E.F(g0[0]), E.F(g0[1]), E.F(g0[0]), E.F(g0[1]),
                  E.L(gx), E.F(gx[0]), E.F(gx[0]), E.L(gy), E.F(gy[0]), E.F(gy[0]), E.L(gs), E.F(gs[0]), E.F(gs[0])))
    txt.append("theorem set_ineq (A B : Finset ℝ) (G : Finset (ℝ × ℝ)) (hG : G ⊆ A ×ˢ B) :\n"
               "    (#(G.image fun q => q.1 - q.2) : ℝ)\n"
               "      ≤ (max (max (#A : ℝ) (#B : ℝ)) (#(G.image fun q => q.1 + q.2) : ℝ)) ^ (%s + %s + %s) :=\n"
               "  set_form (by norm_num) (by norm_num) (by norm_num) (fun Γ p hinj hp hs => entropy_ineq Γ p hinj hp hs) A B G hG\n"
               % (lam_s(l10), lam_s(l01), lam_s(l11)))
    txt.append("theorem set_ineq' (A B : Finset ℝ) (G : Finset (ℝ × ℝ)) (hG : G ⊆ A ×ˢ B) :\n"
               "    (#(G.image fun q => q.1 - q.2) : ℝ)\n"
               "      ≤ (max (max (#A : ℝ) (#B : ℝ)) (#(G.image fun q => q.1 + q.2) : ℝ)) ^ %s := by\n"
               "  have e : %s + %s + %s = %s := by norm_num\n"
               "  rw [← e]\n  exact set_ineq A B G hG\n"
               % (lam_s(Ctot), lam_s(l10), lam_s(l01), lam_s(l11), lam_s(Ctot)))
    txt.append("end %s\n" % ns)
    open(os.path.join(base, "Final.lean"), "w").write("\n".join(txt))
    # General: the entropy form without injectivity (random-selection reduction, EntropyBounds/Glue/Shuffle.lean)
    gt = ["import %s.Final\nimport EntropyBounds.Glue.Shuffle\n" % mod,
          "/-!\n# `%s`: the entropy form without injectivity\n\n"
          "`entropy_ineq_general`: `H(X − Y) ≤ λ₁₀ H(X) + λ₀₁ H(Y) + λ₁₁ H(X + Y)` for every finitely supported pair of real\n"
          "random variables (GGSTW Problem 6.30(a), entropy form), from `entropy_ineq` by `entropy_of_injective`;\n"
          "`entropy_max`: `H(X − Y) ≤ C max(H(X), H(Y), H(X + Y))`, `C = %s`.\n-/\n" % (certname, Ctot),
          "namespace %s\n" % ns, opens,
          "theorem entropy_ineq_general (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (hp : ∀ q ∈ Γ, 0 ≤ p q)\n"
          "    (hs : ∑ q ∈ Γ, p q = 1) :\n"
          "    pushEntropy Γ p (fun q => q.1 - q.2) ≤ %s * pushEntropy Γ p (fun q => q.1) + %s * pushEntropy Γ p (fun q => q.2)\n"
          "      + %s * pushEntropy Γ p (fun q => q.1 + q.2) :=\n"
          "  entropy_of_injective (by norm_num) (by norm_num) (by norm_num) (fun Γ p hinj hp hs => entropy_ineq Γ p hinj hp hs)\n"
          "    Γ p hp hs\n" % (lam_s(l10), lam_s(l01), lam_s(l11)),
          "theorem entropy_max (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (hp : ∀ q ∈ Γ, 0 ≤ p q) (hs : ∑ q ∈ Γ, p q = 1) :\n"
          "    pushEntropy Γ p (fun q => q.1 - q.2) ≤ %s *\n"
          "      max (max (pushEntropy Γ p (fun q => q.1)) (pushEntropy Γ p (fun q => q.2)))\n"
          "        (pushEntropy Γ p (fun q => q.1 + q.2)) := by\n"
          "  have h := entropy_max_of_injective (a := %s) (b := %s) (c := %s) (by norm_num) (by norm_num) (by norm_num)\n"
          "    (fun Γ p hinj hp hs => entropy_ineq Γ p hinj hp hs) Γ p hp hs\n"
          "  have e : %s + %s + %s = %s := by norm_num\n"
          "  rw [e] at h\n  exact h\n"
          % (lam_s(Ctot), lam_s(l10), lam_s(l01), lam_s(l11), lam_s(l10), lam_s(l01), lam_s(l11), lam_s(Ctot)),
          "end %s\n" % ns]
    open(os.path.join(base, "General.lean"), "w").write("\n".join(gt))
    # the Final file registers lists via E.L above; rewrite Defs with every list
    lines = ["import EntropyBounds.Glue.SetForm\n",
             "/-! Forms and lists of the certificate `%s` (generated by tools/export_glue.py). -/\n" % certname,
             "namespace %s\n" % ns, opens]
    lines.append("abbrev Inj (Γ : Finset (ℝ × ℝ)) : Prop := ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q'\n")
    for f in E.form_order:
        lines.append("def %s : Form %d := %s" % (E.forms[f], N, E.form_lean(f)))
    for lst in E.list_order:
        lines.append("def %s : List (Form %d) := [%s]" % (E.lists[lst], N, ", ".join(E.forms[f] for f in lst)))
    lines.append("\nend %s\n" % ns)
    open(os.path.join(base, "Defs.lean"), "w").write("\n".join(lines))
    print("wrote %s: Defs, Glue, %d Ids files, %d Rows files, Final, General" % (base, len(id_files), len(row_files)))


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("cert")
    ap.add_argument("name")
    ap.add_argument("--rows-per-file", type=int, default=150)
    ap.add_argument("--ids-per-file", type=int, default=200)
    a = ap.parse_args()
    run(a.cert, a.name, a.rows_per_file, a.ids_per_file)
