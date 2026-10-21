#!/usr/bin/env python3
"""Does a cert3 certificate use division?  Compare, for every generator set used, the Q-closure (indep3) with the
Z-closure (HNF lattice + the same injectivity rule).  Coordinates of mutually independent vertices are free, so
integer forms live in Z^n.  Usage: div643.py CERT.json"""
import json, os, sys
from fractions import Fraction
import flint
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import indep3
C = json.load(open(sys.argv[1])); cfg = indep3.Cfg(C['config']); n = cfg.n
def hnf(vs):
    vs = [v for v in vs if any(v)]
    if not vs: return ()
    H = flint.fmpz_mat(vs).hnf()
    return tuple(r for r in (tuple(int(H[i, j]) for j in range(n)) for i in range(H.nrows())) if any(r))
def inlat(L, f): return hnf(list(L) + [f]) == L if any(f) else True
def zcl(gens):
    L = hnf(gens)
    while True:
        grew = False
        for x, y in cfg.D:
            d = [0] * n; d[x], d[y] = 1, -1
            if inlat(L, d):
                for c in (x, y):
                    e = [0] * n; e[c] = 1
                    if not inlat(L, e):
                        L = hnf(list(L) + [e]); grew = True
        if not grew: return L
sets = []
for r in C['rows']:
    t = r['type']
    if t in ('sub', 'mono'):
        K = [list(map(Fraction, g)) for g in r['K']]; i = list(map(Fraction, r['i']))
        sets += [K + [i], K]
        if t == 'sub':
            j = list(map(Fraction, r['j'])); sets += [K + [j], K + [i, j]]
    elif t == 'merge':
        sets.append([list(map(Fraction, g)) for g in r['G']])
    elif t in ('matus4', 'five'):
        V = [[list(map(Fraction, g)) for g in gl] for gl in r['vars']]
        for rr in range(1, len(V) + 1):
            for comb in __import__('itertools').combinations(range(len(V)), rr):
                sets.append([g for k in comb for g in V[k]])
nd = 0; ns = 0; seen = set()
for S in sets:
    if not S or any(any(a.denominator != 1 for a in g) for g in S): continue
    key = tuple(tuple(g) for g in S)
    if key in seen: continue
    seen.add(key); ns += 1
    Q = cfg.closure(S)
    Zl = zcl([[int(a) for a in g] for g in S])
    rowsQ = [[Fraction(p, q) for p, q in row] for row in Q]
    # every Q-closure basis vector, scaled to a primitive integer vector, must lie in the Z-closure
    for row in rowsQ:
        den = 1
        for a in row: den = den * a.denominator // __import__('math').gcd(den, a.denominator)
        iv = [int(a * den) for a in row]
        g = 0
        for a in iv: g = __import__('math').gcd(g, abs(a))
        iv = [a // g for a in iv]
        if not inlat(Zl, iv):
            nd += 1
print(f'generator sets checked: {ns}; Q-closure basis vectors (primitive) not in the Z-closure: {nd}')
