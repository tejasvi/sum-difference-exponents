#!/usr/bin/env python3
"""Which torsion does a 6.30 certificate need?  For m in {2, 3, 6, 30} compute closures over Z[1/m] (a form f is
"m-determined" by S if m^e f lies in the Z-span of S (plus relations-free parametrization) for some e <= 30; the
injectivity rule fires when x_v - y_v is m-determined) and compare with the Q-closures used by the certificate.
If the Z[1/m]-closure equals the Q-closure for every generator set, every deduction is valid in abelian groups in
which multiplication by m is injective (no p-torsion for p | m).  Usage: division_check2.py CERT.json"""
import json, sys, os
from fractions import Fraction
import flint
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import indep_check
C = json.load(open(sys.argv[1])); P = indep_check.build(C); k = P.k; extra = C.get('extra', [])
def ivec(v):
    assert all(Fraction(a).denominator == 1 for a in v)
    return [int(a) for a in v]
def hnf_rows(vecs):
    vecs = [v for v in vecs if any(v)]
    if not vecs: return ()
    H = flint.fmpz_mat(vecs).hnf()
    return tuple(r for r in (tuple(int(H[i, j]) for j in range(k)) for i in range(H.nrows())) if any(r))
def in_lat(L, f): return hnf_rows(list(L) + [f]) == L if any(f) else True
def m_det(L, f, m):
    g = list(f)
    for e in range(31):
        if in_lat(L, g): return True
        g = [m * a for a in g]
    return False
def mclosure(vecs, m):
    L = hnf_rows(vecs)
    while True:
        grew = False
        for v in range(P.n):
            d = ivec([p - q for p, q in zip(P.vx[v], P.vy[v])])
            if m_det(L, d, m):
                for w in (ivec(P.vx[v]), ivec(P.vy[v])):
                    if not m_det(L, w, m):
                        # add w after scaling: w is m-determined iff some m^e w in L; we add w itself to the Z[1/m]-module
                        L = hnf_rows(list(L) + [w]); grew = True
        # saturate: add every ground form that is m-determined (keeps L a Z-lattice containing the Z[1/m]-closure part)
        if not grew: return L
ground = [ivec(P.form(v, s)) for v in range(P.n) for s in P.SL] + [ivec(P.amb(f)) for f in extra]
sets = []
for r in C['rows']:
    if r['type'] in ('sub', 'mono'):
        K = [indep_check.ref_vec(P, g, extra) for g in r['K']]; i = indep_check.ref_vec(P, r['i'], extra)
        if r['type'] == 'sub':
            j = indep_check.ref_vec(P, r['j'], extra); sets += [K + [i], K + [j], K + [i, j], K]
        else:
            sets += [K + [i], K]
    elif r['type'] == 'lemma':
        lb = C['lemmas'][str(r['lemma'])]['base']
        coef = C['lemmas'][str(r['lemma'])]['coef']
        amap = {ch: [indep_check.ref_vec(P, g, extra) for g in a] for ch, a in zip(lb, r['args'])}
        for S in coef:
            sets.append([v for ch in sorted(S) for v in amap[ch]])
    elif r['type'] == 'matus':
        a, b, c, d = ([indep_check.ref_vec(P, g, extra) for g in r[t]] for t in 'abcd')
        for x, y, zz in ((a, b, c), (a, c, b), (b, c, a), (a, b, d), (c, d, []), (a, b, [])):
            sets += [x + zz, y + zz, x + y + zz, zz]
    elif r['type'] == 'ci':
        kind, U, V, newids = P.steps[int(r['step'])]
        old = [P.form(v, s) for v in range(newids[0]) for s in P.SL]
        new = [P.form(v, s) for v in newids for s in P.SL]
        Vv = [P.form(v, s) for v, s in V]
        sets += [Vv + new, old, old + new, Vv]
for e in C['eqlaw']:
    kind, U, V, newids = P.steps[int(e['step'])]
    g = [(int(a[0]), (int(a[1][0]), int(a[1][1]))) for a in e['gens']]
    sets.append([P.form(v, s) for v, s in g])
    sets.append([P.form(v, s) if (v, s) in V else P.form(newids[U.index(v)], s) for v, s in g])
uniq, seen = [], set()
for S in sets:
    key = tuple(tuple(v) for v in S)
    if S and key not in seen:
        seen.add(key); uniq.append(S)
for m in (2, 3, 6, 30):
    bad = 0; badsets = 0
    for S in uniq:
        W = P.closure(S)
        L = mclosure([ivec(v) for v in S], m)
        nb = sum(1 for g in ground if indep_check.in_span(W, [Fraction(a) for a in g], k) and not m_det(L, g, m))
        bad += nb; badsets += nb > 0
    print(f'Z[1/{m}]: generator sets {len(uniq)}; sets whose Q-closure exceeds the Z[1/{m}]-closure: {badsets}; '
          f'ground-form memberships missing: {bad}')
