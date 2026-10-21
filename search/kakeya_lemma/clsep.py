"""On-demand copy-lemma separation for four joint variables (flats).

Given h4 = the entropies of the 15 joins of an ordered quadruple (a, b, c, d) of flats at an LP point and a copy
scheme (steps over the letters a, b, c, d, ...), find the inequality sum_S coef_S H(S) >= 0 over subsets S of
{a, b, c, d} that is a combination sum lam_i e_i + sum mu_j q_j (lam >= 0 on elemental Shannon inequalities of the
extended variables, mu free on the copy equalities, zero on every subset that meets a copy variable) and minimizes
coef . h4 subject to sum lam = 1.  The minimizer is a vertex; its support is solved exactly (Fractions), giving an
exact rational lemma (coef, proof) in the format of check630.py "lemma" rows."""
import json, os, itertools
from fractions import Fraction
from math import lcm
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix

import dfzlemma

HERE = os.path.dirname(os.path.abspath(__file__))
SUBS = [S for r in range(1, 5) for S in itertools.combinations('abcd', r)]   # 15 base subsets
_CACHE = {}


def schemes_dfz():
    E = json.load(open(os.path.join(HERE, 'dfz', 'dfz214.json')))
    out = {}
    for k in sorted(E, key=int):
        out.setdefault(E[k]['raw'], E[k]['steps'])
    return out


def scheme_lp(raw, steps):
    """Constraint matrix (non-base rows + normalization) and per-column base coefficients for a scheme."""
    if raw in _CACHE:
        return _CACHE[raw]
    letters, cols, labels, nsh, _ = dfzlemma.build(dict(w=[1, 1, 0, 0, 1, 0, 0, 1, 0], steps=steps))
    n = len(letters)
    basemask = 15
    nonbase = [m for m in range(1, 1 << n) if m & ~basemask]
    rpos = {m: i for i, m in enumerate(nonbase)}
    r_, c_, v_ = [], [], []
    B = np.zeros((len(cols), 15))
    bpos = {}
    for i, S in enumerate(SUBS):
        bpos[sum(1 << 'abcd'.index(x) for x in S)] = i
    for j, col in enumerate(cols):
        for m, c in col.items():
            if m & ~basemask:
                r_.append(rpos[m]); c_.append(j); v_.append(c)
            else:
                B[j, bpos[m]] += c
        if j < nsh:
            r_.append(len(nonbase)); c_.append(j); v_.append(1.0)
    A = coo_matrix((v_, (r_, c_)), shape=(len(nonbase) + 1, len(cols))).tocsr()
    b = np.zeros(len(nonbase) + 1); b[-1] = 1.0
    bounds = [(0, None)] * nsh + [(None, None)] * (len(cols) - nsh)
    res = (letters, cols, labels, nsh, A, b, B, bounds, rpos, bpos)
    _CACHE[raw] = res
    return res


def separate(h4, raw, steps, tol=1e-9, exact=True):
    """h4: array of 15 values in SUBS order.  Returns (value, lemma or None)."""
    letters, cols, labels, nsh, A, b, B, bounds, rpos, bpos = scheme_lp(raw, steps)
    cost = B @ np.asarray(h4, dtype=np.float64)
    res = linprog(cost, A_eq=A, b_eq=b, bounds=bounds, method='highs-ds')
    if res.status != 0:
        return None, None
    if res.fun > -tol or not exact:
        return res.fun, None
    x = res.x
    supp = [j for j in range(len(cols)) if abs(x[j]) > 1e-10]
    rows = sorted(set(rpos[m] for j in supp for m in cols[j] if m in rpos)) + [len(rpos)]
    rr = {r: i for i, r in enumerate(rows)}
    M = [[Fraction(0)] * (len(supp) + 1) for _ in rows]
    for k, j in enumerate(supp):
        for m, c in cols[j].items():
            if m in rpos:
                M[rr[rpos[m]]][k] += c
        if j < nsh:
            M[rr[len(rpos)]][k] += 1
    M[rr[len(rpos)]][len(supp)] = Fraction(1)
    piv, r = [], 0
    for ci in range(len(supp)):
        p = next((i for i in range(r, len(M)) if M[i][ci] != 0), None)
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        inv = 1 / M[r][ci]
        M[r] = [a * inv for a in M[r]]
        for i in range(len(M)):
            if i != r and M[i][ci] != 0:
                f = M[i][ci]
                M[i] = [a - f * bb for a, bb in zip(M[i], M[r])]
        piv.append(ci); r += 1
    if any(M[i][len(supp)] != 0 for i in range(r, len(M))):
        return res.fun, None
    free = [k for k in range(len(supp)) if k not in piv]
    xf = {k: Fraction(float(x[supp[k]])).limit_denominator(10 ** 6) for k in free}
    sol = {}
    for i, k in enumerate(piv):
        sol[supp[k]] = M[i][len(supp)] - sum(M[i][f] * xf[f] for f in free)
    for f in free:
        sol[supp[f]] = xf[f]
    sol = {j: v for j, v in sol.items() if v != 0}
    if any(v < 0 for j, v in sol.items() if j < nsh):
        return res.fun, None
    tot = {}
    for j, v in sol.items():
        for m, c in cols[j].items():
            tot[m] = tot.get(m, 0) + v * c
    if any(v != 0 for m, v in tot.items() if m & ~15):
        return res.fun, None
    coef = {}
    for S in SUBS:
        m = sum(1 << 'abcd'.index(x) for x in S)
        if tot.get(m, 0) != 0:
            coef[''.join(S)] = tot[m]
    if not coef:
        return res.fun, None
    scale = lcm(*[v.denominator for v in coef.values()])
    from math import gcd
    g = 0
    for v in coef.values():
        g = gcd(g, int(v * scale))
    scale = Fraction(scale, g)
    coef = {k: int(v * scale) for k, v in coef.items()}
    proof = [list(labels[j]) + [f'{(v * scale).numerator}/{(v * scale).denominator}'] for j, v in sorted(sol.items())]
    val = sum(coef[''.join(S)] * float(h4[i]) for i, S in enumerate(SUBS) if ''.join(S) in coef)
    lemma = dict(base='abcd', vars=''.join(letters), coef=coef, proof=proof,
                 steps=[dict(new=''.join(st['new']), src=[''.join(g) for g in st['src']], over=''.join(st['over']))
                        for st in steps], source=f'copy-lemma separation, scheme {raw}')
    return val, lemma


def quad_flats(J, a, b, c, d):
    """Flats of the 15 joins in SUBS order (J supports J[x, y] for y in {b, c, d})."""
    ab, ac, ad = J[a, b], J[a, c], J[a, d]
    bc, bd, cd = J[b, c], J[b, d], J[c, d]
    abc, abd, acd, bcd = J[ab, c], J[ab, d], J[ac, d], J[bc, d]
    abcd = J[abc, d]
    m = dict(a=a, b=b, c=c, d=d, ab=ab, ac=ac, ad=ad, bc=bc, bd=bd, cd=cd, abc=abc, abd=abd, acd=acd, bcd=bcd,
             abcd=abcd)
    return [int(m[''.join(S)]) for S in SUBS]


def lemma_terms(flats15, coef):
    """{flat: coef} of the row sum_S coef_S H(join S)."""
    t = {}
    for i, S in enumerate(SUBS):
        k = coef.get(''.join(S), 0)
        if k:
            f = flats15[i]
            t[f] = t.get(f, 0) + k
    return {f: k for f, k in t.items() if k != 0 and f != 0}


def lemma_key(L):
    return json.dumps([sorted(L['coef'].items()), L['steps']], sort_keys=True)
