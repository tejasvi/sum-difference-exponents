#!/usr/bin/env python3
"""Numerical validation of a certificate in the format read by checker/check3.py on actual finite sets X, Y in Z (my own code).

For each (X, Y) and each choice of representatives Gamma (one pair per difference; first, last or random choice):
  copy 0: D vertices iid uniform on Gamma, W vertices with law mu^{*a} * nu^{*b}, all independent (exact product law);
  copy 1: the same for Gamma' = {(-y, -x)} (laws mu' = law(-Y1), nu' = law(-X1)).
Every row is evaluated with the TRUE entropies of its generator tuples (no closures), grid values from exact
convolution powers, L = log|X-Y|, S = log|X+Y|.  Checks: inequality rows >= 0, equality rows = 0, every closure used
(cl(G) from indep3) is a function of G on the support, and sum mult*R = lambda S - L numerically; finally L <= lambda S.
Usage: python -I val643.py CERT.json NRAND SEED"""
import json
import math
import os
import sys
from fractions import Fraction

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import indep3  # noqa: E402


def law_from_values(vals):
    u, c = np.unique(np.asarray(vals, dtype=np.int64), return_counts=True)
    return dict(zip(u.tolist(), (c / c.sum()).tolist()))


def conv(a, b):
    out = {}
    for x, p in a.items():
        for y, q in b.items():
            out[x + y] = out.get(x + y, 0.0) + p * q
    return out


def power(m, k):
    r = {0: 1.0}
    for _ in range(k):
        r = conv(r, m)
    return r


def ent(d):
    p = np.array([v for v in d.values() if v > 0])
    return float(-(p * np.log(p)).sum())


class World:
    def __init__(self, C, X, Y, gamma_choice, rng):
        X, Y = sorted(set(X)), sorted(set(Y))
        self.L = math.log(len({x - y for x in X for y in Y}))
        self.S = math.log(len({x + y for x in X for y in Y}))
        self.M = int(C['grid_depth'])
        cfg = C['config']
        self.n = int(cfg['coords'])
        reps = {}
        for x in X:
            for y in Y:
                reps.setdefault(x - y, []).append((x, y))
        gamma = []
        for d, lst in sorted(reps.items()):
            if gamma_choice == 'first':
                gamma.append(lst[0])
            elif gamma_choice == 'last':
                gamma.append(lst[-1])
            else:
                gamma.append(lst[int(rng.integers(len(lst)))])
        mu = law_from_values([x for x, _ in gamma])
        nu = law_from_values([y for _, y in gamma])
        # grid h(i, j) for 0 <= i, j <= M
        self.h = {}
        mup = [power(mu, i) for i in range(self.M + 1)]
        nup = [power(nu, j) for j in range(self.M + 1)]
        for i in range(self.M + 1):
            for j in range(self.M + 1):
                self.h[(i, j)] = ent(conv(mup[i], nup[j]))
        self.copies = []
        for cp in (0, 1):
            G = gamma if cp == 0 else [(-y, -x) for x, y in gamma]
            m1 = law_from_values([x for x, _ in G])
            n1 = law_from_values([y for _, y in G])
            # product law over vertices
            atoms = [np.zeros((1, self.n), dtype=np.int64)]
            probs = [np.ones(1)]
            A = np.zeros((1, self.n), dtype=np.int64)
            P = np.ones(1)
            for v in cfg['vertices']:
                cs = [int(c) for c in v['coords']]
                if v['type'] == 'D':
                    vals = np.array(G, dtype=np.int64)
                    pv = np.full(len(G), 1.0 / len(G))
                else:
                    a, b = (int(t) for t in v['ij'])
                    law = conv(power(m1, a), power(n1, b))
                    vals = np.array([[k] for k in law], dtype=np.int64)
                    pv = np.array(list(law.values()))
                nA = np.repeat(A, len(vals), axis=0)
                nA[:, cs] = np.tile(vals, (len(A), 1))
                P = np.repeat(P, len(vals)) * np.tile(pv, len(A))
                A = nA
            self.copies.append((A, P))
        self.cache = {}

    def H(self, cp, gens):
        if not gens:
            return 0.0
        key = (cp, tuple(tuple(g) for g in gens))
        if key not in self.cache:
            A, P = self.copies[cp]
            F = np.array([[float(a) for a in g] for g in gens])
            vals = A @ F.T
            vals = np.round(vals * 720720).astype(np.int64)  # forms have small rational coefficients
            _, inv = np.unique(vals, axis=0, return_inverse=True)
            q = np.bincount(inv.ravel(), weights=P)
            q = q[q > 0]
            self.cache[key] = float(-(q * np.log(q)).sum())
        return self.cache[key]

    def functional(self, cp, gens, g):
        A, P = self.copies[cp]
        F = np.array([[float(a) for a in x] for x in gens])
        Xv = np.round((A @ F.T) * 720720).astype(np.int64)
        y = np.round((A @ np.array([float(a) for a in g])) * 720720).astype(np.int64)
        return len(np.unique(Xv, axis=0)) == len(np.unique(np.column_stack([Xv, y]), axis=0))


NSSTAT = []


def row_value(W, cfgobj, r, closures_seen, nonfunc):
    t = r['type']
    cp = int(r.get('copy', 0))
    v = lambda f: [Fraction(a) for a in f]  # noqa: E731

    def Hc(gens):
        k = tuple(tuple(g) for g in gens)
        if gens and (cp, k) not in closures_seen:
            closures_seen.add((cp, k))
            key = cfgobj.closure(gens)
            for row in key:
                g = [Fraction(p, q) for p, q in row]
                if not W.functional(cp, gens, g):
                    nonfunc[0] += 1
        return W.H(cp, gens)
    if t in ('sub', 'mono'):
        K = [v(g) for g in r['K']]
        i = v(r['i'])
        if t == 'mono':
            return Hc(K + [i]) - Hc(K), True
        j = v(r['j'])
        return Hc(K + [i]) + Hc(K + [j]) - Hc(K + [i, j]) - Hc(K), True
    e = lambda c: [Fraction(int(k == c)) for k in range(W.n)]  # noqa: E731
    if t == 'ci':
        new = [int(c) for c in r['new']]
        old = [int(c) for c in r['old']]
        return Hc([e(c) for c in old + new]) - Hc([e(c) for c in old]) - Hc([e(c) for c in new]), False
    if t in ('merge', 'pmerge'):
        # pmerge evaluated with TRUE entropies of G and tau G on the actual product law (validity test of the rule)
        perm = {c: c for c in range(W.n)}
        for a, b in r['perm']:
            perm[int(a)] = int(b)
        G = [v(g) for g in r['G']]
        tG = []
        for g in G:
            hh = [Fraction(0)] * W.n
            for c in range(W.n):
                hh[perm[c]] += g[c]
            tG.append(hh)
        return Hc(tG) - Hc(G), False
    if t == 'bsum':
        return W.S - Hc([v(r['f'])]), True
    if t == 'bdiff':
        return W.L - Hc([v(r['f'])]), True
    if t == 'batom':
        return W.S - Hc([v(r['f'])]), True
    if t == 'dpair':
        x, y = cfgobj.D[int(r['vertex'])]
        return W.L - Hc([e(x), e(y)]), False
    if t == 'ident':
        i, j = (int(a) for a in r['ij'])
        if cp == 1:
            i, j = j, i
        return W.h[(i, j)] - Hc([v(r['f'])]), False
    if t == 'xshare':
        # H_0(tau G) - H_1(G), (tau g)_map(c) = -g_c, with TRUE entropies of the two independently built configurations
        G = [v(g) for g in r['G']]
        mp = {int(a): int(b) for a, b in r['map']}
        pG = []
        for g in G:
            hh = [Fraction(0)] * W.n
            for c_, b_ in mp.items():
                hh[b_] -= g[c_]
            pG.append(hh)
        return W.H(0, pG) - W.H(1, G), False
    if t == 'rshare':
        # H_0(phi G) - H_1(G) with phi: x_k -> -y_k, y_k -> -x_k on D coordinates and w_a -> -w_b for wmap a -> b
        # (true entropies: copy 1 is the independently built reflected configuration with its own W laws)
        G = [v(g) for g in r['G']]
        wm = {int(a): int(b) for a, b in r.get('wmap', [])}
        pG = []
        for g in G:
            hh = [Fraction(0)] * W.n
            for x_, y_ in cfgobj.D:
                hh[x_] = -g[y_]
                hh[y_] = -g[x_]
            for a_, b_ in wm.items():
                hh[b_] = -g[a_]
            pG.append(hh)
        return W.H(0, pG) - W.H(1, G), False
    if t in ('matus4', 'five'):
        V = [[v(g) for g in gl] for gl in r['vars']]

        def J(*ks):
            out = []
            for k_ in ks:
                out += V[k_]
            return out

        def Iv(p, q, rr=None):
            zc = J(rr) if rr is not None else []
            return Hc(J(p) + zc) + Hc(J(q) + zc) - Hc(J(p, q) + zc) - Hc(zc)
        if t == 'matus4':
            sv = int(r['s'])
            ing = -Iv(0, 1) + Iv(0, 1, 2) + Iv(0, 1, 3) + Iv(2, 3)
            NSSTAT.append(ing)
            return Iv(1, 2, 0) + sv * ing + sv * (sv + 1) / 2 * (Iv(0, 2, 1) + Iv(0, 1, 2)), True
        kv = int(r['k'])
        kk = kv * (kv - 1) / 2
        if r['variant'] == 'abcd':
            ing = -Iv(0, 1) + Iv(0, 1, 2) + Iv(0, 1, 3) + Iv(2, 3)
        else:
            ing = -Iv(0, 2) + Iv(0, 2, 1) + Iv(0, 2, 3) + Iv(1, 3)
        NSSTAT.append(ing)
        if r['fam'] == 'M':
            return Iv(1, 4, 0) + kv * (ing + Iv(0, 4, 1) + Iv(0, 1, 4)) + kk * (Iv(0, 2, 1) + Iv(0, 1, 2)), True
        return Iv(0, 1, 4) + kv * (ing + Iv(0, 4, 1) + Iv(1, 4, 0)) + kk * (Iv(0, 2, 1) + Iv(1, 2, 0)), True
    h = W.h
    ij = r.get('ij', [])
    if t == 'g_h00':
        return -h[(0, 0)], False
    if t == 'g_h11':
        return W.S - h[(1, 1)], True
    i, j = (int(a) for a in ij)
    if t == 'g_nonneg':
        return h[(i, j)], True
    if t == 'g_monox':
        return h[(i + 1, j)] - h[(i, j)], True
    if t == 'g_monoy':
        return h[(i, j + 1)] - h[(i, j)], True
    if t == 'g_concx':
        return 2 * h[(i + 1, j)] - h[(i, j)] - h[(i + 2, j)], True
    if t == 'g_concy':
        return 2 * h[(i, j + 1)] - h[(i, j)] - h[(i, j + 2)], True
    if t == 'g_link':
        return h[(i + 1, j)] + h[(i, j + 1)] - h[(i, j)] - W.L, True
    raise ValueError(t)


def validate(C, X, Y, choice, rng):
    W = World(C, X, Y, choice, rng)
    cfgobj = indep3.Cfg(C['config'])
    lam = float(Fraction(C['claimed_lambda']))
    minineq, maxeq, tot = float('inf'), 0.0, 0.0
    seen, nonfunc = set(), [0]
    NSSTAT.clear()
    nsmin = float('inf')
    for r in C['rows']:
        val, ineq = row_value(W, cfgobj, r, seen, nonfunc)
        if r['type'] in ('matus4', 'five'):
            nsmin = min(nsmin, val)
        tot += float(Fraction(r['mult'])) * val
        if ineq:
            minineq = min(minineq, val)
        else:
            maxeq = max(maxeq, abs(val))
    return dict(L=W.L, S=W.S, ratio=W.L / W.S if W.S > 0 else float('nan'), minineq=minineq, maxeq=maxeq,
                resid=tot - (lam * W.S - W.L), gap=lam * W.S - W.L, nonfunc=nonfunc[0], ncl=len(seen),
                nsmin=nsmin, ingneg=sum(1 for x in NSSTAT if x < -1e-12), ingmin=min(NSSTAT) if NSSTAT else float('nan'),
                atoms=len(W.copies[0][1]))


if __name__ == '__main__':
    C = json.load(open(sys.argv[1]))
    nrand, seed = int(sys.argv[2]), int(sys.argv[3])
    rng = np.random.default_rng(seed)
    fixed = [([0, 1, 3], [0, 1, 3]), ([0, 1, 3], [0, 2, 3]), ([0, 1, 4, 6], [0, 2, 3]), ([0, 1, 2, 3], [0, 5, 10]),
             ([0, 2, 3, 4, 7, 11, 12, 14], [-14, -12, -11, -7, -4, -3, -2, 0]),   # MSTD A, Y = -A: |X-Y| > |X+Y|
             ([0, 1, 3, 7, 12], [0, 1, 3, 7, 12]), ([0, 3, 4], [0, 1, 5, 7])]
    sets = [] if '--random-only' in sys.argv else [(X, Y, ch) for X, Y in fixed for ch in ('first', 'last', 'rand')]
    for t in range(nrand):
        nx, ny = int(rng.integers(1, 7)), int(rng.integers(1, 7))
        box = int(rng.choice([4, 8, 15]))
        X = sorted(set(int(a) for a in rng.integers(0, box, size=nx)))
        Y = sorted(set(int(a) for a in rng.integers(0, box, size=ny)))
        sets.append((X, Y, 'rand'))
    worst = dict(minineq=float('inf'), maxeq=0.0, resid=0.0, nonfunc=0, gap=float('inf'), nsmin=float('inf'),
                 ingneg=0, ingmin=float('inf'))
    over = 0
    for X, Y, ch in sets:
        o = validate(C, X, Y, ch, rng)
        worst['minineq'] = min(worst['minineq'], o['minineq'])
        worst['maxeq'] = max(worst['maxeq'], o['maxeq'])
        worst['resid'] = max(worst['resid'], abs(o['resid']))
        worst['nonfunc'] += o['nonfunc']
        worst['gap'] = min(worst['gap'], o['gap'])
        worst['nsmin'] = min(worst['nsmin'], o['nsmin'])
        worst['ingneg'] += o['ingneg']
        if o['ingmin'] == o['ingmin']:
            worst['ingmin'] = min(worst['ingmin'], o['ingmin'])
        over += o['L'] > o['S'] + 1e-12
        if (X, Y) in [(a, b) for a, b in fixed] and ch == 'first':
            print(f"X={X} Y={Y}: L/S={o['ratio']:.4f} atoms={o['atoms']} min ineq {o['minineq']:.2e} max|eq| "
                  f"{o['maxeq']:.2e} resid {o['resid']:.2e} closures {o['ncl']} nonfunc {o['nonfunc']} gap {o['gap']:.4f}",
                  flush=True)
    print(f"{len(sets)} (X, Y, Gamma) cases ({over} with |X-Y| > |X+Y|): min inequality row {worst['minineq']:.2e}, "
          f"max |equality row| {worst['maxeq']:.2e}, max |identity residual| {worst['resid']:.2e}, nonfunctional closure "
          f"elements {worst['nonfunc']}, min (lambda S - L) {worst['gap']:.4f}; non-Shannon rows: min value "
          f"{worst['nsmin']:.2e}, Ingleton-negative instances {worst['ingneg']}, min Ingleton part {worst['ingmin']:.4f}")
