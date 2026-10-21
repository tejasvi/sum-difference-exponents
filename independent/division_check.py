#!/usr/bin/env python3
"""Does the certificate use division?  For every generator set appearing in the certificate (Shannon rows, CI rows,
eqlaw pairs, target), compare the Q-closure (span over Q + injectivity) with the Z-closure (span over Z +
injectivity) on the ground set.  If they agree everywhere, every functional dependence used is valid in ANY abelian
group (the copy relations of this scheme are integral as well), i.e. the inequality would hold in all abelian groups."""
import json, os, sys
from fractions import Fraction
import flint
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import indep_check
C = json.load(open(sys.argv[1])); P = indep_check.build(C)
k = P.k
def ivec(v):
    assert all(Fraction(a).denominator == 1 for a in v), v
    return [int(a) for a in v]
def hnf_rows(vecs):
    vecs = [v for v in vecs if any(v)]
    if not vecs: return ()
    H = flint.fmpz_mat(vecs).hnf()
    rows = [tuple(int(H[i, j]) for j in range(k)) for i in range(H.nrows())]
    return tuple(r for r in rows if any(r))
def in_lat(L, f):
    return hnf_rows(list(L) + [f]) == L if any(f) else True
def zclosure(vecs):
    L = hnf_rows(vecs)
    while True:
        grew = False
        for v in range(P.n):
            d = ivec([p - q for p, q in zip(P.vx[v], P.vy[v])])
            if in_lat(L, d):
                for w in (ivec(P.vx[v]), ivec(P.vy[v])):
                    if not in_lat(L, w):
                        L = hnf_rows(list(L) + [w]); grew = True
        if not grew: return L
extra = C.get('extra', [])
ground = [ivec(P.form(v, s)) for v in range(P.n) for s in P.SL] + [ivec(P.amb(f)) for f in extra]
sets = []
for r in C['rows']:
    if r['type'] in ('sub', 'mono'):
        K = [indep_check.ref_vec(P, g, extra) for g in r['K']]
        i = indep_check.ref_vec(P, r['i'], extra)
        if r['type'] == 'sub':
            j = indep_check.ref_vec(P, r['j'], extra)
            sets += [K + [i], K + [j], K + [i, j], K]
        else:
            sets += [K + [i], K]
    elif r['type'] == 'matus':
        a, b, c, d = ([indep_check.ref_vec(P, g, extra) for g in r[k]] for k in 'abcd')
        for x, y, z in ((a, b, c), (a, c, b), (b, c, a), (a, b, d), (c, d, []), (a, b, [])):
            sets += [x + z, y + z, x + y + z, z]
    else:
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
sets.append([P.form(0, (1, 0)), P.form(0, (0, 1))])
sets += [[P.form(0, tuple(int(x) for x in key.split(',')))] for key in C['lambda']]
seen = set(); ndiff = 0; nsets = 0
for S in sets:
    key = tuple(tuple(v) for v in S)
    if key in seen: continue
    seen.add(key); nsets += 1
    W = P.closure(S); L = zclosure([ivec(v) for v in S])
    for f in ground:
        inQ = indep_check.in_span(W, [Fraction(a) for a in f], k)
        inZ = in_lat(L, f)
        if inQ != inZ:
            ndiff += 1
            if ndiff <= 5: print('division used: set', [list(map(int, v)) for v in S], 'form', f)
print(f'generator sets checked: {nsets}; ground forms in Q-closure but not in Z-closure: {ndiff}')
# denominators needed
from collections import Counter
den = Counter()
seen2 = set()
for S in sets:
    key = tuple(tuple(v) for v in S)
    if key in seen2: continue
    seen2.add(key)
    W = P.closure(S); L = zclosure([ivec(v) for v in S])
    for f in ground:
        if indep_check.in_span(W, [Fraction(a) for a in f], k) and not in_lat(L, f):
            c = next((c for c in range(2, 50) if in_lat(L, [c * a for a in f])), None)
            den[c] += 1
print('minimal multipliers c with c*f in Z-closure:', dict(den))
