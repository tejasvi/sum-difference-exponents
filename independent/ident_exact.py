#!/usr/bin/env python3
"""EXACT check of every grid identification (ident row) of a cert3 certificate on actual small sets X, Y in Z:
build the exact product law (Fractions) of the configuration in both copies (copy 1 from Gamma' = {(-y,-x)}),
compute the exact pmf of each identified form f, and compare it with the exact pmf of mu^{*i} * nu^{*j} (copy 0) or
of mu'^{*i} * nu'^{*j} (copy 1, mu' = law(-Y1), nu' = law(-X1)), and also its entropy with h(i,j) resp. h(j,i).
Also checks that w - v (if W's w, v exist) is NOT equal in law to mu*mu in general (it is mu * refl(mu)).
Usage: ident_exact.py CERT.json NSETS SEED"""
import json, sys, math, itertools
from fractions import Fraction
import numpy as np

C = json.load(open(sys.argv[1])); NS, SEED = int(sys.argv[2]), int(sys.argv[3])
rng = np.random.default_rng(SEED)
cfg = C['config']; n = int(cfg['coords'])

def law(vals):
    d = {}
    for v in vals:
        d[v] = d.get(v, Fraction(0)) + Fraction(1, len(vals))
    return d
def conv(a, b):
    out = {}
    for x, p in a.items():
        for y, q in b.items():
            out[x + y] = out.get(x + y, Fraction(0)) + p * q
    return out
def power(m, k):
    r = {0: Fraction(1)}
    for _ in range(k):
        r = conv(r, m)
    return r
def ent(d):
    return -sum(float(p) * math.log(float(p)) for p in d.values() if p > 0)
def pushforward(atoms, f):
    out = {}
    for vec, p in atoms:
        val = sum(Fraction(c) * x for c, x in zip(f, vec))
        out[val] = out.get(val, Fraction(0)) + p
    return out

def check_sets(X, Y):
    X, Y = sorted(set(X)), sorted(set(Y))
    reps = {}
    for x in X:
        for y in Y:
            reps.setdefault(x - y, []).append((x, y))
    gamma = [lst[int(rng.integers(len(lst)))] for d, lst in sorted(reps.items())]
    mu = law([x for x, _ in gamma]); nu = law([y for _, y in gamma])
    results = []
    for cp in (0, 1):
        G = gamma if cp == 0 else [(-y, -x) for x, y in gamma]
        m1 = law([x for x, _ in G]); n1 = law([y for _, y in G])
        atoms = [((0,) * n, Fraction(1))]
        for v in cfg['vertices']:
            cs = [int(c) for c in v['coords']]
            if v['type'] == 'D':
                vals = [((a, b), Fraction(1, len(G))) for a, b in G]
            else:
                a, b = (int(t) for t in v['ij'])
                L = conv(power(m1, a), power(n1, b))
                vals = [((k,), p) for k, p in L.items()]
            new = []
            for vec, p in atoms:
                for val, q in vals:
                    vv = list(vec)
                    for c, x in zip(cs, val):
                        vv[c] = x
                    new.append((tuple(vv), p * q))
            atoms = new
        for r in C['rows']:
            if r['type'] != 'ident' or int(r['copy']) != cp:
                continue
            f = [Fraction(a) for a in r['f']]
            i, j = (int(a) for a in r['ij'])
            target = conv(power(m1, i), power(n1, j))     # copy's own marginals: exact law of an (i,j) independent sum
            got = pushforward(atoms, f)
            hij = conv(power(mu, i if cp == 0 else j), power(nu, j if cp == 0 else i))   # h index as used by the checker
            same_law = {k: v for k, v in got.items() if v} == {k: v for k, v in target.items() if v}
            same_H = abs(ent(got) - ent(hij)) < 1e-12
            results.append((cp, tuple(r['f']), (i, j), same_law, same_H))
        # w - v control (W coordinates of equal law)
        ws = [int(v['coords'][0]) for v in cfg['vertices'] if v['type'] == 'W']
        if len(ws) >= 2:
            f = [0] * n; f[ws[0]] = 1; f[ws[1]] = -1
            got = pushforward(atoms, f)
            fp = [0] * n; fp[ws[0]] = 1; fp[ws[1]] = 1
            gotp = pushforward(atoms, fp)        # law of w + v (an identified independent sum)
            results.append((cp, 'w-v control', None, {k: v for k, v in got.items() if v} == {k: v for k, v in gotp.items() if v}, None))
    return results

allok, nctl_diff, total = True, 0, 0
fixed = [([0, 1, 3], [0, 2, 3]), ([0, 1, 4], [0, 1, 2]), ([0, 2, 3, 7], [0, 1, 5])]
sets = fixed + [(sorted(set(int(a) for a in rng.integers(0, 7, size=int(rng.integers(2, 5))))),
                 sorted(set(int(a) for a in rng.integers(0, 7, size=int(rng.integers(2, 5)))))) for _ in range(NS)]
for X, Y in sets:
    for cp, f, ij, same_law, same_H in check_sets(X, Y):
        if f == 'w-v control':
            nctl_diff += (not same_law)
            continue
        total += 1
        if not (same_law and same_H):
            allok = False
            print('MISMATCH', X, Y, 'copy', cp, f, ij, same_law, same_H)
print(f'{len(sets)} set pairs: {total} identifications checked exactly (law of the form == mu^i*nu^j as exact pmf, and '
      f'entropy == h(i,j) as indexed by the checker): {"ALL EXACT" if allok else "MISMATCHES"}; '
      f'w - v law differs from the law of w + v in {nctl_diff} of {2 * len(sets)} copy-cases (so w - v must not be identified with w+v-type grid entries)')
