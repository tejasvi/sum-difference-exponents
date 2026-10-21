"""Exact copy-lemma proofs of the DFZ four-variable inequalities (dfz/dfz214.json).

For entry k (9 integers w and copy steps), variables a, b, c, d plus the copy variables.  A step
{new, src, over}: the new variables (one per src item; an item may be a joint group of existing variables) satisfy
  (i)  (new, over) has the law of (src, over):  H(S) = H(phi(S)) for every S in new u over meeting new, where phi
       replaces each new variable by its source group;
  (ii) new is conditionally independent of all earlier variables given over:
       H(new u over) + H(old) - H(new u old) - H(over) = 0.
A proof is target = sum_i lam_i e_i + sum_j mu_j q_j with lam >= 0 on the elemental Shannon inequalities e_i of the
extended variable set and mu free on the equalities q_j; target is the DFZ expression (>= 0).
python dfzlemma.py [K ...]  -> dfz/lemmas.json (all 214 by default)"""
import sys, json, itertools, time
from fractions import Fraction
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix

import os
HERE = os.path.dirname(os.path.abspath(__file__))


def target_dict(w):
    """{frozenset of letters: coef} of -a I(A;B) + b I(A;B|C) + ... + i I(C;D|A)."""
    t = {}

    def I(x, y, z=''):
        return [(x + z, 1), (y + z, 1), (x + y + z, -1), (z, -1)]

    parts = [(-w[0], I('a', 'b')), (w[1], I('a', 'b', 'c')), (w[2], I('a', 'c', 'b')), (w[3], I('b', 'c', 'a')),
             (w[4], I('a', 'b', 'd')), (w[5], I('a', 'd', 'b')), (w[6], I('b', 'd', 'a')), (w[7], I('c', 'd')),
             (w[8], I('c', 'd', 'a'))]
    for k, terms in parts:
        for s, c in terms:
            S = frozenset(s)
            if S:
                t[S] = t.get(S, 0) + k * c
    return {S: v for S, v in t.items() if v != 0}


def build(entry):
    letters = list('abcd') + [x for st in entry['steps'] for x in st['new']]
    n = len(letters)
    idx = {x: i for i, x in enumerate(letters)}
    full = (1 << n) - 1

    def mask(S):
        m = 0
        for x in S:
            m |= 1 << idx[x]
        return m
    cols, labels = [], []      # each column: dict mask -> coef
    for i in range(n):
        cols.append({full: 1, full & ~(1 << i): -1}); labels.append(('mono', letters[i]))
    for i, j in itertools.combinations(range(n), 2):
        rest = [k for k in range(n) if k not in (i, j)]
        for r in range(len(rest) + 1):
            for K in itertools.combinations(rest, r):
                Km = sum(1 << k for k in K)
                cols.append({Km | 1 << i: 1, Km | 1 << j: 1, Km | 1 << i | 1 << j: -1, Km: -1})
                labels.append(('sub', letters[i], letters[j], ''.join(letters[k] for k in K)))
    nshannon = len(cols)
    have = list('abcd')
    for t, st in enumerate(entry['steps']):
        new, src, over = st['new'], st['src'], st['over']
        pool = new + over
        for r in range(1, len(pool) + 1):
            for S in itertools.combinations(pool, r):
                if not any(x in new for x in S):
                    continue
                img = set(x for x in S if x in over)
                for x in S:
                    if x in new:
                        img |= set(src[new.index(x)])
                cols.append({mask(S): 1, mask(img): -1}); labels.append(('eqlaw', t, ''.join(S)))
        old = list(have)
        cols.append({mask(new + over): 1, mask(old): 1, mask(new + old): -1, mask(over): -1})
        labels.append(('ci', t))
        have += new
    # drop the empty set (H = 0) and zero entries
    cols = [{m: c for m, c in col.items() if m != 0 and c != 0} for col in cols]
    tgt = {mask(S): v for S, v in target_dict(entry['w']).items()}
    return letters, cols, labels, nshannon, tgt


def solve(entry):
    letters, cols, labels, nsh, tgt = build(entry)
    n = len(letters)
    nrow = (1 << n) - 1
    r_, c_, v_ = [], [], []
    for j, col in enumerate(cols):
        for m, c in col.items():
            r_.append(m - 1); c_.append(j); v_.append(c)
    A = coo_matrix((v_, (r_, c_)), shape=(nrow, len(cols))).tocsr()
    b = np.zeros(nrow)
    for m, v in tgt.items():
        b[m - 1] = v
    cost = np.array([1.0] * nsh + [0.0] * (len(cols) - nsh))
    bounds = [(0, None)] * nsh + [(None, None)] * (len(cols) - nsh)
    res = linprog(cost, A_eq=A, b_eq=b, bounds=bounds, method='highs-ds')
    if res.status != 0:
        return None, f'LP status {res.status} {res.message}'
    x = res.x
    supp = [j for j in range(len(cols)) if abs(x[j]) > 1e-9]
    # exact solve on the support (Fractions, Gauss-Jordan); free variables fixed to rounded floats
    rowsupp = sorted(set(m for j in supp for m in cols[j]) | set(tgt))
    rpos = {m: i for i, m in enumerate(rowsupp)}
    M = [[Fraction(0)] * (len(supp) + 1) for _ in rowsupp]
    for k, j in enumerate(supp):
        for m, c in cols[j].items():
            M[rpos[m]][k] = Fraction(c)
    for m, v in tgt.items():
        M[rpos[m]][len(supp)] = Fraction(v)
    piv, r = [], 0
    for cidx in range(len(supp)):
        p = next((i for i in range(r, len(M)) if M[i][cidx] != 0), None)
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        inv = 1 / M[r][cidx]
        M[r] = [a * inv for a in M[r]]
        for i in range(len(M)):
            if i != r and M[i][cidx] != 0:
                f = M[i][cidx]
                M[i] = [a - f * bb for a, bb in zip(M[i], M[r])]
        piv.append(cidx); r += 1
    if any(M[i][len(supp)] != 0 for i in range(r, len(M))):
        return None, 'inconsistent on support'
    free = [k for k in range(len(supp)) if k not in piv]
    xf = {k: Fraction(float(x[supp[k]])).limit_denominator(10 ** 6) for k in free}
    sol = {}
    for rr, k in enumerate(piv):
        val = M[rr][len(supp)] - sum(M[rr][f] * xf[f] for f in free)
        sol[supp[k]] = val
    for f in free:
        sol[supp[f]] = xf[f]
    sol = {j: v for j, v in sol.items() if v != 0}
    if any(v < 0 for j, v in sol.items() if j < nsh):
        return None, 'negative Shannon multiplier after exact solve'
    # exact verification
    tot = {}
    for j, v in sol.items():
        for m, c in cols[j].items():
            tot[m] = tot.get(m, 0) + v * c
    keys = set(tot) | set(tgt)
    if any(tot.get(m, 0) != tgt.get(m, 0) for m in keys):
        return None, 'identity fails'
    proof = []
    for j, v in sorted(sol.items()):
        lab = labels[j]
        proof.append(list(lab) + [f'{v.numerator}/{v.denominator}'])
    return dict(w=entry['w'], vars=''.join(letters), raw=entry['raw'],
                steps=[dict(new=''.join(st['new']), src=[''.join(g) for g in st['src']], over=''.join(st['over']))
                       for st in entry['steps']], proof=proof), None


if __name__ == '__main__':
    E = json.load(open(f'{HERE}/dfz/dfz214.json'))
    ks = [str(k) for k in sys.argv[1:]] or sorted(E, key=int)
    out, fails = {}, []
    t0 = time.time()
    for k in ks:
        L, err = solve(E[k])
        if L is None:
            fails.append((k, err)); print('FAIL', k, E[k]['w'], E[k]['raw'], err, flush=True)
        else:
            out[k] = L
    print(f'{len(out)} proved, {len(fails)} failed  [{time.time()-t0:.0f}s]', flush=True)
    path = f'{HERE}/dfz/lemmas.json' if not sys.argv[1:] else f'{HERE}/dfz/lemmas_partial.json'
    json.dump(out, open(path, 'w'))
    print('wrote', path)
