#!/usr/bin/env python3
"""Semantic validation of a certificate in the format read by checker/check630.py on ACTUAL glued distributions.

For a law of (X, Y) (integer support, x - y injective) we build the joint law of all vertices by the copy
lemma (U' sampled from the conditional law of U given the V-forms, independently of everything else), then:
  (a) every vertex is distributed exactly as (X, Y) (up to float rounding of probabilities);
  (b) the parametrized linear relations hold on every atom;
  (c) every CI row evaluates to 0, every Shannon row to >= 0 (entropies of the GENERATOR tuples);
  (d) every eqlaw pair has equal laws (as distributions of value tuples);
  (e) every closure used is functionally determined by its generators on the support;
  (f) H(g0) + sum mult*row  -  sum lambda_r H(pi_r(g0)) = 0 numerically, with true entropies;
  (g) H(X,Y) <= sum lambda_r H(pi_r) (the claimed inequality) on the law itself.
Usage: python -I numeric_validate.py CERT.json NRANDOM [SEED]
"""
import json
import math
import os
import sys
from fractions import Fraction

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import indep_check  # noqa: E402

D = (1, -1)


def amb_std(n, v, s):
    f = np.zeros(2 * n, dtype=np.int64)
    f[2 * v], f[2 * v + 1] = s
    return f


def copy_step(A, p, U, Vforms):
    """A: N x 2n int atoms, p: N probs. Return new atoms with copies of vertices U appended."""
    N = A.shape[0]
    Vv = A @ np.array(Vforms, dtype=np.int64).T if Vforms else np.zeros((N, 0), dtype=np.int64)
    _, vk = np.unique(Vv, axis=0, return_inverse=True)
    vk = vk.ravel()
    PV = np.bincount(vk, weights=p)
    Ucols = [2 * u + c for u in U for c in (0, 1)]
    Uv = A[:, Ucols]
    key = np.concatenate([vk[:, None], Uv], axis=1)
    T, tinv = np.unique(key, axis=0, return_inverse=True)
    tinv = tinv.ravel()
    pT = np.bincount(tinv, weights=p)
    order = np.argsort(T[:, 0], kind='stable')
    T, pT = T[order], pT[order]
    starts = np.searchsorted(T[:, 0], np.arange(len(PV)), side='left')
    ends = np.searchsorted(T[:, 0], np.arange(len(PV)), side='right')
    cnt = (ends - starts)[vk]
    rep = np.repeat(np.arange(N), cnt)
    offs = np.concatenate([np.arange(c) for c in cnt]) if N else np.zeros(0, dtype=np.int64)
    tidx = starts[vk][rep] + offs
    newA = np.concatenate([A[rep], T[tidx, 1:]], axis=1)
    newp = p[rep] * pT[tidx] / PV[vk[rep]]
    keep = newp > 0
    return newA[keep], newp[keep]


def entropy_of(A, p, F):
    if len(F) == 0:
        return 0.0
    vals = A @ np.array(F, dtype=np.int64).T
    _, inv = np.unique(vals, axis=0, return_inverse=True)
    q = np.bincount(inv.ravel(), weights=p)
    q = q[q > 0]
    return float(-(q * np.log(q)).sum())


def law_of(A, p, F):
    vals = A @ np.array(F, dtype=np.int64).T
    u, inv = np.unique(vals, axis=0, return_inverse=True)
    q = np.bincount(inv.ravel(), weights=p)
    return {tuple(r): w for r, w in zip(u.tolist(), q)}


def functional(A, F, g):
    """Is the form g a function of the forms F on the atoms of A?"""
    if len(F) == 0:
        return len(np.unique(A @ g)) == 1
    X = A @ np.array(F, dtype=np.int64).T
    Y = np.concatenate([X, (A @ g)[:, None]], axis=1)
    return len(np.unique(X, axis=0)) == len(np.unique(Y, axis=0))


def glue(C, pts, w):
    n_final = 1 + sum(len(st['U']) for st in C['steps'])
    A = np.array([[x, y] for x, y in pts], dtype=np.int64)
    p = np.array(w, dtype=float)
    n = 1
    for st in C['steps']:
        Vf = []
        for v, s in st['V']:
            f = np.zeros(2 * n, dtype=np.int64)
            f[2 * v], f[2 * v + 1] = s
            Vf.append(f)
        A, p = copy_step(A, p, list(st['U']), Vf)
        n += len(st['U'])
    assert n == n_final and A.shape[1] == 2 * n
    return A, p


def validate(C, P, pts, w, tol=1e-9, check_closures=True):
    """P: indep_check.Param configuration built from C."""
    n = P.n
    A, p = glue(C, pts, w)
    out = {'atoms': len(p)}
    base = {}
    for (x, y), wi in zip(pts, w):
        base[(x, y)] = base.get((x, y), 0) + wi
    # (a) vertex marginals
    errA = 0.0
    for v in range(n):
        L = law_of(A, p, [amb_std(n, v, (1, 0)), amb_std(n, v, (0, 1))])
        keys = set(L) | set(base)
        errA = max(errA, max(abs(L.get(k, 0) - base.get(k, 0)) for k in keys))
    out['marg_err'] = errA
    # (b) relations: every ambient vector in the kernel of the parametrization vanishes on the atoms
    #     test: for random integer combos r of the kernel basis
    M = np.array([[float(a) for a in (P.vx[v] if c == 0 else P.vy[v])] for v in range(n) for c in (0, 1)])
    # kernel of M^T (2n x k): vectors r with r @ M = 0
    from fractions import Fraction as Fr
    kerb = indep_check.nullspace_rows(indep_check.rref_basis(
        [[Fr(P.vx[v][j]) if c == 0 else Fr(P.vy[v][j]) for v in range(n) for c in (0, 1)]
         for j in range(P.k)], 2 * n), 2 * n)
    relerr = 0
    for r in kerb:
        den = math.lcm(*[a.denominator for a in r])
        ri = np.array([int(a * den) for a in r], dtype=np.int64)
        relerr = max(relerr, int(np.abs(A @ ri).max()))
    out['rel_rank'] = len(kerb)
    out['rel_err'] = relerr
    extra = [np.array(f, dtype=np.int64) for f in C.get('extra', [])]

    def amb_of(ref):
        if ref[0] == 'amb':
            return extra[int(ref[1])]
        return amb_std(n, int(ref[0]), (int(ref[1][0]), int(ref[1][1])))

    cacheH = {}

    def H(F):
        key = tuple(tuple(int(a) for a in f) for f in F)
        key = tuple(sorted(set(key)))
        if key not in cacheH:
            cacheH[key] = entropy_of(A, p, [np.array(k, dtype=np.int64) for k in key])
        return cacheH[key]

    # ground set for closure checks
    ground = [amb_std(n, v, s) for v in range(n) for s in P.SL] + extra
    gpar = [P.amb(list(g)) for g in ground]
    total = H([amb_std(n, 0, (1, 0)), amb_std(n, 0, (0, 1))])
    minrow = float('inf')
    slack = 0.0
    ci_max = 0.0
    nclos, nonfunc = 0, 0
    checked = set()

    def closure_check(F):
        nonlocal nclos, nonfunc
        key = tuple(sorted(set(tuple(int(a) for a in f) for f in F)))
        if key in checked or not check_closures:
            return
        checked.add(key)
        W = P.closure([P.amb(list(f)) for f in F])
        nclos += 1
        for g, gp in zip(ground, gpar):
            if indep_check.in_span(W, gp, P.k):
                if not functional(A, F, g):
                    nonfunc += 1

    matus_min, ing_min, ing_neg = [float('inf')], [float('inf')], [0]
    for r in C['rows']:
        m = float(Fraction(r['mult']))
        if r['type'] in ('sub', 'mono'):
            K = [amb_of(g) for g in r['K']]
            i = amb_of(r['i'])
            if r['type'] == 'sub':
                j = amb_of(r['j'])
                val = H(K + [i]) + H(K + [j]) - H(K + [i, j]) - H(K)
                for F in (K + [i], K + [j], K + [i, j], K):
                    closure_check(F)
            else:
                val = H(K + [i]) - H(K)
                for F in (K + [i], K):
                    closure_check(F)
            minrow = min(minrow, val)
        elif r['type'] == 'matus':
            sv = int(r['s'])
            a_, b_, c_, d_ = ([amb_of(g) for g in r[k]] for k in 'abcd')

            def Iv(x, y, z):
                return H(x + z) + H(y + z) - H(x + y + z) - H(z)
            ing = Iv(a_, b_, c_) + Iv(a_, b_, d_) + Iv(c_, d_, []) - Iv(a_, b_, [])
            val = (sv * (sv + 3) / 2 * Iv(a_, b_, c_) + sv * (sv + 1) / 2 * Iv(a_, c_, b_) + Iv(b_, c_, a_)
                   + sv * Iv(a_, b_, d_) + sv * Iv(c_, d_, []) - sv * Iv(a_, b_, []))
            matus_min[0] = min(matus_min[0], val)
            ing_min[0] = min(ing_min[0], ing)
            if ing < -1e-12:
                ing_neg[0] += 1
            for x, y, z in ((a_, b_, c_), (a_, c_, b_), (b_, c_, a_), (a_, b_, d_), (c_, d_, []), (a_, b_, [])):
                for F in (x + z, y + z, x + y + z, z):
                    if F:
                        closure_check(F)
            minrow = min(minrow, val)
        else:
            kind, U, V, newids = P.steps[int(r['step'])]
            old = [amb_std(n, v, s) for v in range(newids[0]) for s in ((1, 0), (0, 1))]
            new = [amb_std(n, v, s) for v in newids for s in ((1, 0), (0, 1))]
            Vf = [amb_std(n, v, s) for v, s in V]
            val = H(Vf + new) + H(old) - H(old + new) - H(Vf)
            ci_max = max(ci_max, abs(val))
        slack += m * val
        total += m * val
    lam = {tuple(int(x) for x in k.split(',')): float(Fraction(v)) for k, v in C['lambda'].items()}
    rhs = sum(v * H([amb_std(n, 0, s)]) for s, v in lam.items())
    out['identity_residual'] = total - rhs
    out['matus_min'] = matus_min[0]
    out['matus_ingleton_min'] = ing_min[0]
    out['matus_ingleton_negative'] = ing_neg[0]
    out['min_shannon_row'] = minrow
    out['max_abs_ci'] = ci_max
    out['slack'] = slack
    # (d) eqlaw laws
    eqerr = 0.0
    for e in C['eqlaw']:
        kind, U, V, newids = P.steps[int(e['step'])]
        gens, img = [], []
        for g in e['gens']:
            v, s = int(g[0]), (int(g[1][0]), int(g[1][1]))
            gens.append(amb_std(n, v, s))
            img.append(amb_std(n, v, s) if (v, s) in V else amb_std(n, newids[U.index(v)], s))
        L1, L2 = law_of(A, p, gens), law_of(A, p, img)
        keys = set(L1) | set(L2)
        eqerr = max(eqerr, max(abs(L1.get(k, 0) - L2.get(k, 0)) for k in keys))
    out['eqlaw_err'] = eqerr
    out['closures_checked'] = nclos
    out['closure_nonfunctional'] = nonfunc
    # (g) the claimed inequality on the law itself
    hX = entropy_of(A[:, :2], p, [np.array([1, 0]), np.array([0, 1])])
    hx = entropy_of(A[:, :2], p, [np.array([1, 0])])
    hy = entropy_of(A[:, :2], p, [np.array([0, 1])])
    hs = entropy_of(A[:, :2], p, [np.array([1, 1])])
    out['H'] = (hX, hx, hy, hs)
    out['ineq_gap'] = sum(v * entropy_of(A[:, :2], p, [np.array(s_)]) for s_, v in lam.items()) - hX
    ok = (errA < tol and relerr == 0 and abs(out['identity_residual']) < 1e-8 and minrow > -1e-9
          and ci_max < 1e-8 and eqerr < tol and nonfunc == 0 and out['ineq_gap'] > -1e-9)
    out['ok'] = ok
    return out


def random_law(rng, m, box):
    pts = set()
    diffs = set()
    while len(pts) < m:
        x, y = (int(a) for a in rng.integers(-box, box + 1, size=2))
        if (x, y) in pts or (x - y) in diffs:
            continue
        pts.add((x, y))
        diffs.add(x - y)
    pts = sorted(pts)
    w = rng.dirichlet(np.full(m, rng.choice([0.3, 1.0, 3.0])))
    return pts, list(w)


def mi_law():
    path = os.environ.get('MI13_LAW', 'certificate_3b_13pt.json')
    c = json.load(open(path))
    pts = [(w['x'], w['y']) for w in c['weights']]
    ws = [Fraction(w['num'], w['den']) for w in c['weights']]
    s = sum(ws)
    return pts, [float(x / s) for x in ws]


if __name__ == '__main__':
    C = json.load(open(sys.argv[1]))
    nrand = int(sys.argv[2])
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    P = indep_check.build(C)
    rng = np.random.default_rng(seed)
    laws = [('MI 13-point', *mi_law())]
    for t in range(nrand):
        box = int(rng.choice([2, 3, 5, 8]))
        m = int(rng.integers(2, min(15, 4 * box + 1) + 1))
        laws.append((f'random m={m} box={box}', *random_law(rng, m, box)))
    nok = 0
    worst = {}
    for li, (name, pts, w) in enumerate(laws):
        o = validate(C, P, pts, w, check_closures=(li <= 60))
        nok += o['ok']
        for k in ('marg_err', 'rel_err', 'max_abs_ci', 'eqlaw_err', 'closure_nonfunctional'):
            worst[k] = max(worst.get(k, 0), o[k])
        worst['max|identity_residual|'] = max(worst.get('max|identity_residual|', 0), abs(o['identity_residual']))
        worst['min_shannon_row'] = min(worst.get('min_shannon_row', 1e9), o['min_shannon_row'])
        worst['min_ineq_gap'] = min(worst.get('min_ineq_gap', 1e9), o['ineq_gap'])
        worst['matus_min'] = min(worst.get('matus_min', 1e9), o['matus_min'])
        worst['matus_ingleton_min'] = min(worst.get('matus_ingleton_min', 1e9), o['matus_ingleton_min'])
        worst['matus_ingleton_negative_total'] = worst.get('matus_ingleton_negative_total', 0) + o['matus_ingleton_negative']
        if name.startswith('MI') or not o['ok']:
            hX, hx, hy, hs = o['H']
            print(f"{name}: atoms={o['atoms']} ok={o['ok']} resid={o['identity_residual']:.2e} "
                  f"minrow={o['min_shannon_row']:.2e} ci={o['max_abs_ci']:.1e} eq={o['eqlaw_err']:.1e} "
                  f"closures={o['closures_checked']} nonfunc={o['closure_nonfunctional']} relrank={o['rel_rank']} "
                  f"relerr={o['rel_err']} margerr={o['marg_err']:.1e}")
            print(f"   H(X,Y)={hX:.10f} H(X)={hx:.10f} H(Y)={hy:.10f} H(X+Y)={hs:.10f} "
                  f"ratio={hX / max(hx, hy, hs):.10f}  RHS-LHS={o['ineq_gap']:.6e}  slack={o['slack']:.6e}")
    print(f"{nok}/{len(laws)} laws fully consistent; worst: {worst}")
