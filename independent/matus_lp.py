#!/usr/bin/env python3
"""Independent verification that the Matus family, as implemented in check630.py,
    M_s(a,b,c,d) = I(b;c|a) + s*(I(a;b|c) + I(a;b|d) + I(c;d) - I(a;b)) + s(s+1)/2*(I(a;c|b) + I(a;b|c)) >= 0,
is a valid information inequality for every s = 1..SMAX, by induction on s (DFZ arXiv:1104.3602, Rule [1]):
  M_0 = I(b;c|a) >= 0 is Shannon.  For s >= 1, with five variables A,B,C,D,R where R is a copy of A over (B,C)
  (i.e. (R,B,C) has the law of (A,B,C) and R is conditionally independent of (A,D) given (B,C); such R exists for
  every joint law by the copy lemma), M_s(A,B,C,D) is a nonnegative combination of elemental Shannon inequalities
  on the 5 variables, the copy equalities, and the premise M_{s-1}(AR, BR, CR, D) >= 0 (joint variables).
For each s an exact rational certificate is found (HiGHS for the support, then exact Fraction solve on the support)
and checked exactly.  Usage: python -I matus_lp.py SMAX
"""
import sys
import itertools
from fractions import Fraction

import numpy as np
from scipy.optimize import linprog

A, B, Cv, Dv, R = 1, 2, 4, 8, 16
NV = 5
FULL = 31


def H(S):
    v = [Fraction(0)] * 32
    if S:
        v[S] += 1
    return v


def add(*terms):
    out = [Fraction(0)] * 32
    for c, v in terms:
        for i in range(32):
            if v[i]:
                out[i] += c * v[i]
    return out


def I(X, Y, Z=0):
    return add((1, H(X | Z)), (1, H(Y | Z)), (-1, H(X | Y | Z)), (-1, H(Z)))


def M(s, a, b, c, d):
    s = Fraction(s)
    cc = s * (s + 1) / 2
    return add((1, I(b, c, a)), (s, I(a, b, c)), (s, I(a, b, d)), (s, I(c, d)), (-s, I(a, b)),
               (cc, I(a, c, b)), (cc, I(a, b, c)))


def shannon_rows():
    rows = []
    for i in range(NV):
        rows.append(('mono', add((1, H(FULL)), (-1, H(FULL & ~(1 << i))))))
    for i, j in itertools.combinations(range(NV), 2):
        others = [k for k in range(NV) if k not in (i, j)]
        for r in range(len(others) + 1):
            for K in itertools.combinations(others, r):
                Km = sum(1 << k for k in K)
                rows.append((f'I({i};{j}|{Km})', I(1 << i, 1 << j, Km)))
    return rows


def copy_rows():
    eq = []
    for T in (0, B, Cv, B | Cv):
        eq.append(('eqlaw', add((1, H(R | T)), (-1, H(A | T)))))
    eq.append(('ci', I(R, A | Dv, B | Cv)))
    return eq


def solve(s):
    target = M(s, A, B, Cv, Dv)
    ineq = shannon_rows()
    prem = M(s - 1, A | R, B | R, Cv | R, Dv)
    ineq.append(('premise', prem))
    eqs = copy_rows()
    cols = [r for _, r in ineq] + [r for _, r in eqs] + [[-x for x in r] for _, r in eqs]
    Aeq = np.array([[float(col[k]) for col in cols] for k in range(1, 32)])
    beq = np.array([float(target[k]) for k in range(1, 32)])
    res = linprog(np.ones(len(cols)), A_eq=Aeq, b_eq=beq, bounds=[(0, None)] * len(cols), method='highs')
    if res.status != 0:
        return None, f'LP status {res.status}'
    x = res.x
    nI = len(ineq)
    supp_i = [k for k in range(nI) if x[k] > 1e-9]
    # free equality multipliers: nu = x[nI + j] - x[nI + len(eqs) + j]
    # exact solve on support: unknowns = mu (supp_i) and nu (all eqs, free)
    unk = [('i', k) for k in supp_i] + [('e', j) for j in range(len(eqs))]
    rowsM = []
    for k in range(1, 32):
        row = []
        for t, idx in unk:
            row.append(ineq[idx][1][k] if t == 'i' else eqs[idx][1][k])
        row.append(target[k])
        rowsM.append(row)
    # Gaussian elimination (exact)
    m, n = len(rowsM), len(unk)
    piv_cols, r = [], 0
    Mx = [list(rw) for rw in rowsM]
    for ccol in range(n):
        p = next((i for i in range(r, m) if Mx[i][ccol] != 0), None)
        if p is None:
            continue
        Mx[r], Mx[p] = Mx[p], Mx[r]
        pv = Mx[r][ccol]
        Mx[r] = [v / pv for v in Mx[r]]
        for i in range(m):
            if i != r and Mx[i][ccol] != 0:
                f = Mx[i][ccol]
                Mx[i] = [a - f * b for a, b in zip(Mx[i], Mx[r])]
        piv_cols.append(ccol)
        r += 1
    if any(all(v == 0 for v in Mx[i][:n]) and Mx[i][n] != 0 for i in range(m)):
        return None, 'exact system inconsistent on support'
    sol = [Fraction(0)] * n
    for i, ccol in enumerate(piv_cols):
        sol[ccol] = Mx[i][n]
    # if free columns exist, try the float values for them (rounded) and recompute pivots
    free = [cidx for cidx in range(n) if cidx not in piv_cols]
    if free:
        fl = {}
        for cidx in free:
            t, idx = unk[cidx]
            val = x[idx] if t == 'i' else x[nI + idx] - x[nI + len(eqs) + idx]
            fl[cidx] = Fraction(val).limit_denominator(10**6)
        for i, ccol in enumerate(piv_cols):
            sol[ccol] = Mx[i][n] - sum(Mx[i][cf] * fl[cf] for cf in free)
        for cf in free:
            sol[cf] = fl[cf]
    mu = {unk[cidx][1]: sol[cidx] for cidx in range(n) if unk[cidx][0] == 'i'}
    nu = {unk[cidx][1]: sol[cidx] for cidx in range(n) if unk[cidx][0] == 'e'}
    if any(v < 0 for v in mu.values()):
        return None, 'negative multiplier after exact solve'
    # exact verification of the identity
    tot = add(*[(mu[k], ineq[k][1]) for k in mu], *[(nu[j], eqs[j][1]) for j in nu])
    if any(tot[k] != target[k] for k in range(32)):
        return None, 'exact identity fails'
    return dict(mu={ineq[k][0]: v for k, v in mu.items()}, nu={eqs[j][0] + str(j): v for j, v in nu.items()},
                premise=mu.get(len(ineq) - 1, Fraction(0))), 'ok'


if __name__ == '__main__':
    smax = int(sys.argv[1])
    allok = True
    for s in range(1, smax + 1):
        cert, msg = solve(s)
        if cert is None:
            allok = False
            print(f's={s}: FAILED ({msg})')
        else:
            print(f's={s}: M_s proved from M_(s-1)(AR,BR,CR,D) [multiplier {cert["premise"]}], copy R of A over BC, '
                  f'{len(cert["mu"])} Shannon/premise rows; exact identity verified')
    print('ALL s VERIFIED' if allok else 'SOME FAILED')
