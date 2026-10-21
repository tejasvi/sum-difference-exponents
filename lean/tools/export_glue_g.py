#!/usr/bin/env python3
"""Export a sum-difference entropy certificate (check630.py format) as Lean modules over an abelian group `G` in which
doubling is injective (no 2-torsion): EntropyBounds/GlueG/Certs/NAME.

Usage: python3 -I tools/export_glue_g.py CERT.json NAME

The pipeline is that of export_glue.py, which is imported and not modified (its outputs for EntropyBounds/Glue are
unchanged).  Three things differ:

* Closures and determination witnesses are computed over Z[1/2] instead of Q: every multiplier `c` (and `wc` in rule
  INJ) is a power of two, found from an integer echelon basis of the generators (the Lean checker `GlueG.checkDWR`
  verifies `isPow2` again).  Rule INJ is applied in rounds as before.
* A closure class is represented by the forms of a fixed pool that lie in its Z[1/2]-closure (the pool: all forms of
  the lists the exporter uses, and the coordinates and differences of the vertices, minus the forms in the span of
  the relations).  Two lists with the same rational closure must get the same representative; this is checked here,
  so the certificate's rows combine exactly as over Q.
* The Lean text is written for `G`: `G × G` for `ℝ × ℝ`, `Conf N G`, `Hyp` with the field `two` (injective doubling)
  passed to every witness check, the hypothesis `h2` in the final theorems, namespace `EntropyBounds.GlueG.Certs.NAME`.
  The certificate's Lemmas module (lemmas stated for any value type) is reused from EntropyBounds/Glue/Certs/NAME and
  must be byte-identical to the one this run generates.

Intermediate outputs of export_glue.py go to scratch/export_g/ (pass 1: rational closures, to collect the lists;
pass 2: Z[1/2] closures).
"""
import sys, os, io, contextlib, collections, shutil, re
from fractions import Fraction as Fr

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import export_glue as eg  # noqa: E402  (unchanged)

ROOT = os.path.dirname(HERE)
SCRATCH = os.path.join(ROOT, "scratch", "export_g")


# ----------------------------------------------------------------------------------------------------------------
# Z[1/2] linear algebra

def int_echelon(vecs):
    """Integer echelon basis of the lattice spanned by vecs, with integer transforms: [(pivot, (vec, combo))]."""
    n = len(vecs)
    m = len(vecs[0]) if vecs else 0
    rows = []
    for i, v in enumerate(vecs):
        assert all(Fr(x).denominator == 1 for x in v), "non-integer generator"
        rows.append(([int(x) for x in v], [1 if j == i else 0 for j in range(n)]))
    basis, remaining = [], rows
    for col in range(m):
        nz = [r for r in remaining if r[0][col] != 0]
        if not nz:
            continue
        others = [r for r in remaining if r[0][col] == 0]
        while len(nz) > 1:
            nz.sort(key=lambda r: abs(r[0][col]))
            piv, new = nz[0], [nz[0]]
            for r in nz[1:]:
                q = r[0][col] // piv[0][col]
                v = [a - q * b for a, b in zip(r[0], piv[0])]
                t = [a - q * b for a, b in zip(r[1], piv[1])]
                (new if v[col] != 0 else others).append((v, t))
            nz = new
        basis.append((col, nz[0]))
        remaining = others
    return basis


def express2(target, vecs):
    """(coeffs, c) with c a power of two and c * target = sum coeffs_i vecs_i over Z, or None.

    The echelon basis b_j of the lattice L spanned by vecs is linearly independent, so the rational coefficients of
    target in it are unique, and target lies in L[1/2] exactly when their denominators are powers of two."""
    t = [Fr(x) for x in target]
    if not vecs:
        return None if any(t) else ([], 1)
    nu = []
    for col, (v, T) in int_echelon(vecs):
        if t[col] != 0:
            cf = t[col] / v[col]
            t = [a - cf * b for a, b in zip(t, v)]
            nu.append((cf, T))
    if any(a != 0 for a in t):
        return None
    c = eg.lcm_den([cf for cf, _ in nu])
    if c & (c - 1):
        return None
    co = [sum(int(cf * c) * T[i] for cf, T in nu) for i in range(len(vecs))]
    return co, c


def in_span2(target, vecs):
    return express2(target, vecs) is not None


def rounds2(self, S):
    S = [list(map(Fr, f)) for f in S]
    out = [list(S)]
    while True:
        span = S + self.R
        new = [k for k in range(self.nv) if in_span2(self.dvec(k), span)
               and not (in_span2(self.unit(k, 0), span) and in_span2(self.unit(k, 1), span))]
        if not new:
            break
        for k in new:
            S = S + [self.unit(k, 0), self.unit(k, 1)]
        out.append(list(S))
    return out


STATS = collections.Counter()


def dwr2(self, S, f):
    """one-round witness for f from S modulo R with multipliers powers of two, or None."""
    Sv = [list(map(Fr, x)) for x in S]
    gens = [k for k in range(self.nv) if in_span2(self.dvec(k), Sv + self.R)]
    aug = Sv + self.R + [self.unit(k, c) for k in gens for c in (0, 1)]
    r = express2(list(map(Fr, f)), aug)
    if r is None:
        return None
    co, c = r
    nS, nR = len(Sv), len(self.R)
    ms, rs = co[:nS], co[nS:nS + nR]
    g = [[0, 0] for _ in range(self.N)]
    for idx, k in enumerate(gens):
        g[k][0] = co[nS + nR + 2 * idx]
        g[k][1] = co[nS + nR + 2 * idx + 1]
    wc = [1] * self.N
    wit = [[] for _ in range(self.N)]
    wr = [[] for _ in range(self.N)]
    for k in range(self.N):
        if g[k] != [0, 0]:
            cw, d = express2(self.dvec(k), Sv + self.R)
            wc[k], wit[k], wr[k] = d, cw[:nS], cw[nS:]
            STATS['wc=%d' % d] += 1
    STATS['c=%d' % c] += 1
    return (c, ms, rs, g, wc, wit, wr)


POOL = []
REP_OF_Q, Q_OF_REP = {}, {}      # consistency of the Z[1/2] representatives with the rational closures


def qkey(self, S):
    """the rational closure of S (export_glue's key, with rational rounds)."""
    last = ORIG['rounds'](self, S)[-1]
    rows = sorted(eg.check630.rref(last + self.R))
    return tuple(tuple(r) for p, r in rows)


def key2(self, S):
    """the closure class of S: the pool forms in its Z[1/2]-closure, in pool order."""
    last = rounds2(self, S)[-1]
    rep = tuple(f for f in POOL if in_span2(list(map(Fr, f)), last + self.R))
    qk = qkey(self, S)
    assert REP_OF_Q.setdefault(qk, rep) == rep, "one rational closure with two Z[1/2] representatives"
    assert Q_OF_REP.setdefault(rep, qk) == qk, "two rational closures with one Z[1/2] representative"
    return rep


def rep2(self, key):
    return key


ORIG = {'rounds': eg.Space.rounds, 'dwr': eg.Space.dwr, 'key': eg.Space.key, 'rep': eg.Space.rep}


# ----------------------------------------------------------------------------------------------------------------
# the Lean text for G

def to_group(txt, fn, name, N):
    mod_old, mod_new = "EntropyBounds.Glue.Certs.%s" % name, "EntropyBounds.GlueG.Certs.%s" % name
    if fn == "Final.lean":
        reps = [
            ("for every finitely supported pair of real random\nvariables with `x − y` injective on the support; "
             "`set_ineq`: for finite `A, B ⊆ ℝ` and `G ⊆ A × B`,\n`|A −_G B| ≤ max(|A|, |B|, |A +_G B|)^C`",
             "for every finitely supported pair of random\nvariables in an abelian group `G` without 2-torsion, with "
             "`x − y` injective on the support; `set_ineq`: for finite\n`A, B ⊆ G` and `P ⊆ A × B`, "
             "`|A −_P B| ≤ max(|A|, |B|, |A +_P B|)^C`"),
            ("(hinj : Inj Γ) (hp : ∀ q ∈ Γ, 0 ≤ p q)",
             "(h2 : ∀ x : G, x + x = 0 → x = 0) (hinj : Inj Γ)\n    (hp : ∀ q ∈ Γ, 0 ≤ p q)"),
            ("have h : Hyp Γ p := ⟨hinj, hp, hs⟩", "have h : Hyp Γ p := ⟨h2, hinj, hp, hs⟩"),
            ("(A B : Finset ℝ) (G : Finset (ℝ × ℝ)) (hG : G ⊆ A ×ˢ B)",
             "(h2 : ∀ x : G, x + x = 0 → x = 0) (A B : Finset G) (P : Finset (G × G))\n    (hP : P ⊆ A ×ˢ B)"),
            ("(#(G.image fun q => q.1 - q.2) : ℝ)", "(#(P.image fun q => q.1 - q.2) : ℝ)"),
            ("(#(G.image fun q => q.1 + q.2) : ℝ)", "(#(P.image fun q => q.1 + q.2) : ℝ)"),
            ("(fun Γ p hinj hp hs => entropy_ineq Γ p hinj hp hs) A B G hG",
             "(fun Γ p hinj hp hs => entropy_ineq Γ p h2 hinj hp hs) A B P hP"),
            ("exact set_ineq A B G hG", "exact set_ineq h2 A B P hP"),
        ]
    elif fn == "General.lean":
        reps = [
            ("for every finitely supported pair of real\nrandom variables",
             "for every finitely supported pair of\nrandom variables in an abelian group `G` without 2-torsion"),
            ("theorem entropy_ineq_general (Γ", "theorem entropy_ineq_general (h2 : ∀ x : G, x + x = 0 → x = 0) (Γ"),
            ("theorem entropy_max (Γ", "theorem entropy_max (h2 : ∀ x : G, x + x = 0 → x = 0) (Γ"),
            ("(fun Γ p hinj hp hs => entropy_ineq Γ p hinj hp hs)", "(fun Γ p hinj hp hs => entropy_ineq Γ p h2 hinj hp hs)"),
        ]
    else:
        reps = []
    for a, b in reps:
        assert a in txt, (fn, a[:60])
        txt = txt.replace(a, b)
    txt = txt.replace("import EntropyBounds.Glue.", "import EntropyBounds.GlueG.")
    txt = txt.replace("import %s.Lemmas" % mod_new, "import %s.Lemmas" % mod_old)
    txt = txt.replace("generated by tools/export_glue.py", "generated by tools/export_glue_g.py")
    txt = txt.replace("open EntropyBounds.Iid EntropyBounds.Glue SumsDifferences",
                      "open EntropyBounds.Iid EntropyBounds.GlueG SumsDifferences")
    txt = txt.replace("ℝ × ℝ", "G × G")
    txt = txt.replace("Conf %d :=" % N, "Conf %d G :=" % N)
    txt = txt.replace("h.inj (hv", "h.two h.inj (hv")
    var = "variable {G : Type} [AddCommGroup G] [DecidableEq G]\n"
    extra = "open %s\n\n" % mod_old if "lem_" in txt else ""
    n_ns = txt.count("namespace %s\n" % mod_old)
    assert n_ns == 1, (fn, n_ns)
    txt = txt.replace("namespace %s\n" % mod_old, "namespace %s\n\n%s%s" % (mod_new, extra, var))
    txt = txt.replace("end %s\n" % mod_old, "end %s\n" % mod_new)
    assert mod_old not in txt.replace("import %s.Lemmas" % mod_old, "").replace("open %s\n" % mod_old, ""), fn
    assert "ℝ × ℝ" not in txt and "EntropyBounds.Glue " not in txt and "EntropyBounds.Glue\n" not in txt, fn
    return txt


def main():
    cert, name = sys.argv[1], sys.argv[2]
    lists = []
    captured = {}
    orig_identity = eg.Exporter.identity
    orig_write = eg.write_files

    def identity_rec(self, lst):
        lists.append(tuple(tuple(int(x) for x in f) for f in lst))
        return orig_identity(self, lst)

    def write_rec(E, *a, **k):
        captured['E'] = E
        return orig_write(E, *a, **k)

    eg.Exporter.identity = identity_rec
    eg.write_files = write_rec
    # pass 1: rational closures, only to collect the lists
    p1 = os.path.join(SCRATCH, "pass1")
    shutil.rmtree(p1, ignore_errors=True)
    eg.ROOT = p1
    with contextlib.redirect_stdout(io.StringIO()):
        eg.run(cert, name, 150, 200)
    E1 = captured['E']
    N, sp = E1.N, E1.final
    pool = set(f for lst in lists for f in lst)
    for k in range(N):
        for v in (sp.unit(k, 0), sp.unit(k, 1), sp.dvec(k)):
            pool.add(tuple(int(x) for x in v))
    POOL[:] = [f for f in sorted(pool) if not in_span2(list(map(Fr, f)), sp.R)]
    print("pass 1: %d lists, pool %d forms" % (len(set(lists)), len(POOL)))
    # pass 2: Z[1/2]
    eg.Exporter.identity = orig_identity
    eg.Space.rounds, eg.Space.dwr, eg.Space.key, eg.Space.rep = rounds2, dwr2, key2, rep2
    p2 = os.path.join(SCRATCH, "pass2")
    shutil.rmtree(p2, ignore_errors=True)
    eg.ROOT = p2
    eg.run(cert, name, 150, 200)
    print("multipliers:", sorted(STATS.items()), "| closure classes:", len(REP_OF_Q))
    assert all(int(k.split("=")[1]) & (int(k.split("=")[1]) - 1) == 0 for k in STATS)
    src = os.path.join(p2, "EntropyBounds", "Glue", "Certs", name)
    dst = os.path.join(ROOT, "EntropyBounds", "GlueG", "Certs", name)
    old_lem = os.path.join(ROOT, "EntropyBounds", "Glue", "Certs", name, "Lemmas.lean")
    os.makedirs(dst, exist_ok=True)
    for fn in sorted(os.listdir(src)):
        txt = open(os.path.join(src, fn), encoding="utf-8").read()
        if fn == "Lemmas.lean":
            assert txt == open(old_lem, encoding="utf-8").read(), "Lemmas.lean differs from the existing module"
            continue
        open(os.path.join(dst, fn), "w", encoding="utf-8").write(to_group(txt, fn, name, N))
    print("wrote", dst)


if __name__ == "__main__":
    main()
