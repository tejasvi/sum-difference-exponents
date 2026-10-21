#!/usr/bin/env python3
"""Independent exact re-derivation of each 'dfz*' lemma of a cert (own copy-lemma LP; the certificate's proof is NOT used).
For lemma L: variables = L['vars'] (letters), copy steps L['steps'] = [{new, src (groups of letters), over}], target
sum_S coef_S H(S) >= 0 (S subsets of base).  Rows: elemental Shannon on all variables (H(all)-H(all-x) >= 0,
I(x;y|K) >= 0), copy equalities per step: H(S) = H(phi S) for every S in new u over meeting new (phi: new letter -> its src
group), and I(new; old | over) = 0 (old = all variables before the step).  HiGHS finds a support; the dual is then solved
EXACTLY (Fractions) on that support and checked: Shannon multipliers >= 0, identity exact.
Usage: dfz_lp.py CERT.json [lemma ids...]"""
import json, sys, itertools
from fractions import Fraction
import numpy as np
from scipy.optimize import linprog

C = json.load(open(sys.argv[1]))
ids = sys.argv[2:] or [k for k in C['lemmas'] if k.startswith('dfz')]


def solve(L):
    letters = L['vars']
    n = len(letters)
    idx = {x: i for i, x in enumerate(letters)}
    full = (1 << n) - 1
    mask = lambda s: sum(1 << idx[x] for x in s)
    def Hv(S):
        v = [Fraction(0)] * (1 << n)
        if S:
            v[S] = Fraction(1)
        return v
    def comb(*terms):
        out = [Fraction(0)] * (1 << n)
        for c, v in terms:
            for i, a in enumerate(v):
                if a:
                    out[i] += c * a
        return out
    def I(X, Y, Z=0):
        return comb((1, Hv(X | Z)), (1, Hv(Y | Z)), (-1, Hv(X | Y | Z)), (-1, Hv(Z)))
    ineq = []
    for i in range(n):
        ineq.append(('mono', comb((1, Hv(full)), (-1, Hv(full & ~(1 << i))))))
    for i, j in itertools.combinations(range(n), 2):
        others = [t for t in range(n) if t not in (i, j)]
        for r in range(len(others) + 1):
            for K in itertools.combinations(others, r):
                ineq.append((f'I({letters[i]};{letters[j]}|{"".join(letters[t] for t in K)})', I(1 << i, 1 << j, sum(1 << t for t in K))))
    eqs = []
    have = set(L['base'])
    for t, st in enumerate(L['steps']):
        new, src, over = st['new'], st['src'], st['over']
        assert len(new) == len(src) and all(x not in have for x in new) and all(x in have for x in over)
        assert all(all(y in have for y in g) for g in src)
        old = set(have)
        pool = list(new) + list(over)
        for r in range(1, len(pool) + 1):
            for S in itertools.combinations(pool, r):
                if not any(x in new for x in S):
                    continue
                img = set(x for x in S if x in over)
                for x in S:
                    if x in new:
                        img |= set(src[new.index(x)])
                eqs.append((f'eq{t}:{"".join(S)}', comb((1, Hv(mask(S))), (-1, Hv(mask(img))))))
        eqs.append((f'ci{t}', comb((1, Hv(mask(set(new) | set(over)))), (1, Hv(mask(old))), (-1, Hv(mask(set(new) | old))), (-1, Hv(mask(over))))))
        have |= set(new)
    target = [Fraction(0)] * (1 << n)
    for key, cv in L['coef'].items():
        target[mask(key)] += Fraction(cv)
    cols = [r for _, r in ineq] + [r for _, r in eqs] + [[-x for x in r] for _, r in eqs]
    Aeq = np.array([[float(col[k]) for col in cols] for k in range(1, 1 << n)])
    beq = np.array([float(target[k]) for k in range(1, 1 << n)])
    res = linprog(np.ones(len(cols)), A_eq=Aeq, b_eq=beq, bounds=[(0, None)] * len(cols), method='highs')
    if res.status != 0:
        return False, f'LP status {res.status} (not implied by these rows)'
    x = res.x
    nI = len(ineq)
    supp = [k for k in range(nI) if x[k] > 1e-9]
    unk = [('i', k) for k in supp] + [('e', j) for j in range(len(eqs))]
    Mx = [[(ineq[i][1][k] if kind == 'i' else eqs[i][1][k]) for kind, i in unk] + [target[k]] for k in range(1, 1 << n)]
    m_, nn = len(Mx), len(unk)
    piv, r = [], 0
    for col in range(nn):
        p = next((i for i in range(r, m_) if Mx[i][col] != 0), None)
        if p is None:
            continue
        Mx[r], Mx[p] = Mx[p], Mx[r]
        pv = Mx[r][col]
        Mx[r] = [v / pv for v in Mx[r]]
        for i in range(m_):
            if i != r and Mx[i][col] != 0:
                f = Mx[i][col]
                Mx[i] = [u - f * w for u, w in zip(Mx[i], Mx[r])]
        piv.append(col)
        r += 1
    if any(all(v == 0 for v in row[:nn]) and row[nn] != 0 for row in Mx):
        return False, 'support system inconsistent'
    free = [col for col in range(nn) if col not in piv]
    sol = [Fraction(0)] * nn
    fl = {}
    for col in free:
        kind, i = unk[col]
        val = x[i] if kind == 'i' else x[nI + i] - x[nI + len(eqs) + i]
        fl[col] = Fraction(val).limit_denominator(10 ** 6)
        sol[col] = fl[col]
    for i, col in enumerate(piv):
        sol[col] = Mx[i][nn] - sum(Mx[i][cf] * fl[cf] for cf in free)
    mu = {unk[col][1]: sol[col] for col in range(nn) if unk[col][0] == 'i'}
    nu = {unk[col][1]: sol[col] for col in range(nn) if unk[col][0] == 'e'}
    if any(v < 0 for v in mu.values()):
        return False, 'negative Shannon multiplier after exact solve'
    tot = comb(*[(mu[k], ineq[k][1]) for k in mu], *[(nu[j], eqs[j][1]) for j in nu])
    if any(tot[k] != target[k] for k in range(1 << n)):
        return False, 'exact identity fails'
    return True, f'{len([v for v in mu.values() if v])} Shannon rows, {len([v for v in nu.values() if v])} copy equalities; max multiplier denominator {max(Fraction(v).denominator for v in list(mu.values()) + list(nu.values()))}'


for lid in ids:
    ok, info = solve(C['lemmas'][lid])
    print(f"{lid}: {'PROVED (own exact copy-lemma LP)' if ok else 'NOT PROVED'} -- {info}", flush=True)
