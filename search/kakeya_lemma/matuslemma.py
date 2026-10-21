"""Exact copy-lemma proofs of the Matus inequalities M_1..M_S as a chain of check630 lemmas.
M_s(a,b,c,d) = I(b;c|a) + s(-I(a;b) + I(a;b|c) + I(a;b|d) + I(c;d)) + s(s+1)/2 (I(a;c|b) + I(a;b|c))  (check630 form).
Lemma matus<s>: r = copy of a over (b, c); proof = Shannon terms + copy equalities + (s >= 2) M_{s-1}(ar, br, cr, d)
(the induction of the audit, following DFZ's rule).  python matuslemma.py S -> dfz/matus_lemmas.json"""
import sys, json, itertools
from fractions import Fraction
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix

import os
HERE = os.path.dirname(os.path.abspath(__file__))


def matus_coef(s):
    t = {}

    def I(x, y, z=''):
        return [(x + z, 1), (y + z, 1), (x + y + z, -1), (z, -1)]
    cc = s * (s + 1) // 2
    for k, terms in [(1, I('b', 'c', 'a')), (-s, I('a', 'b')), (s, I('a', 'b', 'c')), (s, I('a', 'b', 'd')),
                     (s, I('c', 'd')), (cc, I('a', 'c', 'b')), (cc, I('a', 'b', 'c'))]:
        for S, c in terms:
            S = frozenset(S)
            if S:
                t[S] = t.get(S, 0) + k * c
    return {S: v for S, v in t.items() if v != 0}


def build(s):
    letters = 'abcdr'
    n = 5
    idx = {x: i for i, x in enumerate(letters)}
    full = (1 << n) - 1

    def mask(S):
        return sum(1 << idx[x] for x in S)
    cols, labels = [], []
    for i in range(n):
        cols.append({full: 1, full & ~(1 << i): -1}); labels.append(['mono', letters[i]])
    for i, j in itertools.combinations(range(n), 2):
        rest = [k for k in range(n) if k not in (i, j)]
        for r in range(len(rest) + 1):
            for K in itertools.combinations(rest, r):
                Km = sum(1 << k for k in K)
                cols.append({Km | 1 << i: 1, Km | 1 << j: 1, Km | 1 << i | 1 << j: -1, Km: -1})
                labels.append(['sub', letters[i], letters[j], ''.join(letters[k] for k in K)])
    nsh = len(cols)
    for S in ['r', 'rb', 'rc', 'rbc']:
        img = S.replace('r', 'a')
        cols.append({mask(S): 1, mask(img): -1}); labels.append(['eqlaw', 0, S])
    cols.append({mask('rbc'): 1, mask('abcd'): 1, mask('abcdr'): -1, mask('bc'): -1}); labels.append(['ci', 0])
    napply = None
    if s >= 2:
        amap = dict(a='ar', b='br', c='cr', d='d')
        col = {}
        for S, v in matus_coef(s - 1).items():
            m = mask(set(x for y in S for x in amap[y]))
            col[m] = col.get(m, 0) + v
        cols.append(col); labels.append(['apply', f'matus{s-1}', ['ar', 'br', 'cr', 'd']])
        napply = len(cols) - 1
    cols = [{m: c for m, c in col.items() if m != 0 and c != 0} for col in cols]
    tgt = {mask(S): v for S, v in matus_coef(s).items()}
    return cols, labels, nsh, napply, tgt


PATTERN = [('a', 'b', 'dr', '1'), ('a', 'r', 'b', 'cc'), ('a', 'r', 'c', 'cc'), ('a', 'r', 'bcd', 's'),
           ('b', 'r', 'cd', 's'), ('c', 'd', 'r', '1'), ('c', 'r', 'abd', 's'), ('d', 'r', 'a', 's'),
           ('d', 'r', 'b', 's'), ('d', 'r', 'abc', 'ss')]


def prove_pattern(s):
    """M_s = M_{s-1}(ar,br,cr,d) + sum of the audit's ten Shannon terms (coefficients 1, s, s(s+1)/2, s^2) + copy
    equalities; the equality multipliers are solved exactly.  Returns None if the pattern does not close."""
    cols, labels, nsh, napply, tgt = build(s)
    val = dict(s=Fraction(s), cc=Fraction(s * (s + 1), 2), ss=Fraction(s * s))
    val['1'] = Fraction(1)
    lab2j = {tuple(labels[j][1:4]) if labels[j][0] == 'sub' else None: j for j in range(nsh)}
    sol = {}
    for x, y, K, c in PATTERN:
        j = lab2j[(x, y, K)]
        sol[j] = val[c]
    if napply is not None:
        sol[napply] = Fraction(1)
    res = dict((m, Fraction(v)) for m, v in tgt.items())
    for j, v in sol.items():
        for m, c in cols[j].items():
            res[m] = res.get(m, 0) - v * c
    eqj = [j for j in range(nsh, len(cols)) if j != napply]
    rows = sorted(set(m for m, v in res.items() if v != 0) | set(m for j in eqj for m in cols[j]))
    rp = {m: i for i, m in enumerate(rows)}
    M = [[Fraction(0)] * (len(eqj) + 1) for _ in rows]
    for k, j in enumerate(eqj):
        for m, c in cols[j].items():
            M[rp[m]][k] += c
    for m, v in res.items():
        if m in rp:
            M[rp[m]][len(eqj)] = v
    piv, r = [], 0
    for ci in range(len(eqj)):
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
    if any(M[i][len(eqj)] != 0 for i in range(r, len(M))):
        return None
    for i, k in enumerate(piv):
        if M[i][len(eqj)] != 0:
            sol[eqj[k]] = M[i][len(eqj)]
    proof = [list(labels[j]) + [f'{v.numerator}/{v.denominator}'] for j, v in sorted(sol.items()) if v != 0]
    coef = {''.join(sorted(S)): int(v) for S, v in matus_coef(s).items()}
    return dict(base='abcd', vars='abcdr', steps=[dict(new='r', src=['a'], over='bc')], coef=coef, proof=proof,
                source=f'Matus M_{s} by induction (copy of a over bc; M_{s-1} applied to (ar, br, cr, d))')


def prove(s):
    if s >= 2:
        L = prove_pattern(s)
        if L is not None:
            return L
    cols, labels, nsh, napply, tgt = build(s)
    nrow = 31
    r_, c_, v_ = [], [], []
    for j, col in enumerate(cols):
        for m, c in col.items():
            r_.append(m - 1); c_.append(j); v_.append(c)
    A = coo_matrix((v_, (r_, c_)), shape=(nrow, len(cols))).tocsr()
    b = np.zeros(nrow)
    for m, v in tgt.items():
        b[m - 1] = v
    nonneg = set(range(nsh)) | ({napply} if napply is not None else set())
    bounds = [(0, None) if j in nonneg else (None, None) for j in range(len(cols))]
    cost = np.array([1.0 if j < nsh else 0.0 for j in range(len(cols))])
    res = linprog(cost, A_eq=A, b_eq=b, bounds=bounds, method='highs-ds')
    if res.status != 0:
        raise RuntimeError(f's={s}: LP {res.message}')
    x = res.x
    supp = [j for j in range(len(cols)) if abs(x[j]) > 1e-9]
    rows = sorted(set(m for j in supp for m in cols[j]) | set(tgt))
    rp = {m: i for i, m in enumerate(rows)}
    M = [[Fraction(0)] * (len(supp) + 1) for _ in rows]
    for k, j in enumerate(supp):
        for m, c in cols[j].items():
            M[rp[m]][k] += c
    for m, v in tgt.items():
        M[rp[m]][len(supp)] = Fraction(v)
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
        raise RuntimeError(f's={s}: inconsistent support')
    free = [k for k in range(len(supp)) if k not in piv]
    xf = {k: Fraction(float(x[supp[k]])).limit_denominator(10 ** 6) for k in free}
    sol = {}
    for i, k in enumerate(piv):
        sol[supp[k]] = M[i][len(supp)] - sum(M[i][f] * xf[f] for f in free)
    for f in free:
        sol[supp[f]] = xf[f]
    sol = {j: v for j, v in sol.items() if v != 0}
    if any(v < 0 for j, v in sol.items() if j in nonneg):
        raise RuntimeError(f's={s}: negative multiplier')
    proof = []
    for j, v in sorted(sol.items()):
        proof.append(list(labels[j]) + [f'{v.numerator}/{v.denominator}'])
    coef = {''.join(sorted(S)): int(v) for S, v in matus_coef(s).items()}
    return dict(base='abcd', vars='abcdr', steps=[dict(new='r', src=['a'], over='bc')], coef=coef, proof=proof,
                source=f'Matus M_{s} by induction (copy of a over bc; M_{s-1} applied to (ar, br, cr, d))')


if __name__ == '__main__':
    S = int(sys.argv[1])
    import importlib.util
    spec = importlib.util.spec_from_file_location('chk', f'{HERE}/check630.py')
    chk = importlib.util.module_from_spec(spec); spec.loader.exec_module(chk)
    out = {}

    def lookup(lid, depth):
        return chk.verify_lemma(out[lid], lookup, depth)
    done = {}

    def lookup_memo(lid, depth):
        if lid not in done:
            done[lid] = chk.verify_lemma(out[lid], lookup_memo, depth)
        return done[lid]
    for s in range(1, S + 1):
        out[f'matus{s}'] = prove(s)
        base, coef = lookup_memo(f'matus{s}', 0)
        assert {''.join(sorted(k)): v for k, v in coef.items()} == {k: Fraction(v) for k, v in out[f'matus{s}']['coef'].items()}
        if s <= 3 or s % 50 == 0:
            print(s, len(out[f'matus{s}']['proof']), 'entries; verified', flush=True)
    json.dump(out, open(f'{HERE}/dfz/matus_lemmas.json', 'w'))
    print('wrote', len(out))
