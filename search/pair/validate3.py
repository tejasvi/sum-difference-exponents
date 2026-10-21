"""Numerical validation of a cert3 certificate on actual sets X, Y (mutually independent D and W vertices):
every row is evaluated with true entropies; copy 1 uses the reflected pair (-Y, -X) with Gamma' = {(-y,-x)}.
Usage: python validate3.py CERT.json [trials] [seed]"""
import sys, json, math, random
from fractions import Fraction
from collections import defaultdict
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))


def ent(d):
    return -sum(p * math.log(p) for p in d.values() if p > 0)


def conv(a, b):
    out = defaultdict(float)
    for x, p in a.items():
        for y, q in b.items():
            out[x + y] += p * q
    return dict(out)


def power(mu, k):
    r = {0: 1.0}
    for _ in range(k):
        r = conv(r, mu)
    return r


class World:
    def __init__(self, X, Y, M, verts, N):
        X, Y = sorted(set(X)), sorted(set(Y))
        self.L = math.log(len({x - y for x in X for y in Y}))
        self.S = math.log(len({x + y for x in X for y in Y}))
        self.laws, self.grids = [], []
        self.N = N
        for cp in (0, 1):
            XX, YY = (X, Y) if cp == 0 else ([-y for y in Y], [-x for x in X])
            rep = {}
            for x in XX:
                for y in YY:
                    rep.setdefault(x - y, (x, y))
            G = list(rep.values())
            wg = 1.0 / len(G)
            mu = defaultdict(float); nu = defaultdict(float)
            for (x, y) in G:
                mu[x] += wg; nu[y] += wg
            mu, nu = dict(mu), dict(nu)
            law = {(): 1.0}
            for v in verts:      # vertices in coordinate order
                if v['type'] == 'C':
                    # conditional copy: draw the new coordinates from the law of src given the given forms
                    assert list(v['coords']) == list(range(len(next(iter(law))), len(next(iter(law))) + len(v['coords'])))
                    given = [[Fraction(x) for x in g] for g in v['given']]
                    zf = lambda a: tuple(sum(g[c] * a[c] for c in range(len(a)) if g[c]) for g in given)
                    cond = defaultdict(lambda: defaultdict(float))
                    for a, p in law.items():
                        cond[zf(a)][tuple(a[s_] for s_ in v['src'])] += p
                    new = defaultdict(float)
                    for a, p in law.items():
                        cz = cond[zf(a)]
                        tot = sum(cz.values())
                        for sv, q in cz.items():
                            new[a + sv] += p * q / tot
                    law = dict(new)
                    continue
                if v['type'] == 'D':
                    comp = {(x, y): wg for (x, y) in G}
                else:
                    i, j = v['ij']
                    comp = {(z,): p for z, p in conv(power(mu, i), power(nu, j)).items()}
                new = {}
                for a, p in law.items():
                    for b, q in comp.items():
                        new[a + b] = p * q
                law = new
            self.laws.append(law)
            pm = [power(mu, i) for i in range(M + 1)]
            pn = [power(nu, j) for j in range(M + 1)]
            self.grids.append({(i, j): ent(conv(pm[i], pn[j])) for i in range(M + 1) for j in range(M + 1)})
            # multigrid g_f(i,j) = H(a X1 + b Y1 + V_ij)
            mgs = {}
            for (a, b) in ((1, 1), (1, -1)):
                fl = defaultdict(float)
                for (x, y) in G:
                    fl[a * x + b * y] += wg
                fl = dict(fl)
                for i in range(M + 1):
                    for j in range(M + 1):
                        mgs[((a, b), i, j)] = ent(conv(fl, conv(pm[i], pn[j])))
            self.mgs = getattr(self, 'mgs', []) + [mgs]
            if cp == 0:
                self.mu0, self.nu0 = mu, nu
        self.h = self.grids[0]
        self.cache = {}
        self.sgc = {}

    def sg(self, t):
        """signed grid of copy 0: H(a mu + a' (-mu) + b nu + b' (-nu)), independent summands"""
        t = tuple(int(x) for x in t)
        if t not in self.sgc:
            neg = lambda d: {-k: p for k, p in d.items()}
            d = {0: 1.0}
            for law, m in ((self.mu0, t[0]), (neg(self.mu0), t[1]), (self.nu0, t[2]), (neg(self.nu0), t[3])):
                for _ in range(m):
                    d = conv(d, law)
            self.sgc[t] = ent(d)
        return self.sgc[t]

    def H(self, cp, gens):
        key = (cp, tuple(tuple(g) for g in gens))
        if key not in self.cache:
            if not gens:
                self.cache[key] = 0.0
                return 0.0
            if not hasattr(self, 'np_laws'):
                import numpy as np
                self.np_laws = []
                for law in self.laws:
                    ks = list(law)
                    self.np_laws.append((np.array(ks, dtype=np.int64), np.array([law[k] for k in ks])))
            import numpy as np
            from math import lcm
            V, P = self.np_laws[cp]
            Gi = []
            for g in gens:            # integer multiple of each form (a bijective rescaling: same entropy)
                fr = [Fraction(x) for x in g]
                den = 1
                for x in fr:
                    den = lcm(den, x.denominator)
                Gi.append([int(x * den) for x in fr])
            K = V @ np.array(Gi, dtype=np.int64).T
            _, inv = np.unique(K, axis=0, return_inverse=True)
            q = np.bincount(inv.ravel(), weights=P)
            q = q[q > 0]
            self.cache[key] = float(-(q * np.log(q)).sum())
        return self.cache[key]


class MultiWorld:
    """copy c -> configuration c // 2 (World), reflected iff c % 2; grids are configuration independent."""
    def __init__(self, worlds):
        self.ws = worlds
        self.L, self.S, self.N = worlds[0].L, worlds[0].S, worlds[0].N
        self.h = worlds[0].h
        self.grids = worlds[0].grids
        self.mgs = getattr(worlds[0], 'mgs', None)
        self.sg = worlds[0].sg

    def H(self, cp, gens):
        return self.ws[cp // 2].H(cp % 2, gens)


def row_value(W, row, verts):
    t = row['type']
    h = W.h
    N = W.N
    vec = lambda f: [Fraction(x) for x in f]
    e = lambda c: [1 if k == c else 0 for k in range(N)]
    if t in ('sub', 'mono'):
        cp = row['copy']; K = [vec(g) for g in row['K']]; i = vec(row['i'])
        if t == 'mono':
            return W.H(cp, K + [i]) - W.H(cp, K), True
        j = vec(row['j'])
        return W.H(cp, K + [i]) + W.H(cp, K + [j]) - W.H(cp, K + [i, j]) - W.H(cp, K), True
    if t == 'ci':
        cp = row['copy']
        old, new = row['old'], row['new']
        return W.H(cp, [e(c) for c in old + new]) - W.H(cp, [e(c) for c in old]) - W.H(cp, [e(c) for c in new]), False
    if t == 'cci':
        cp = row['copy']; k = row['vertex']
        v = verts[k]
        old = sorted(c for vv in verts[:k] for c in vv['coords'])
        new = sorted(v['coords'])
        given = [vec(g) for g in v['given']]
        return (W.H(cp, [e(c) for c in old + new]) + W.H(cp, given) - W.H(cp, [e(c) for c in old])
                - W.H(cp, given + [e(c) for c in new])), False
    if t == 'cmerge':
        cp = row['copy']; v = verts[row['vertex']]
        G = [vec(g) for g in row['G']]
        pG = []
        for g in G:
            hh = list(g)
            for c, s_ in zip(v['coords'], v['src']):
                hh[s_] += g[c]
                hh[c] = Fraction(0)
            pG.append(hh)
        return W.H(cp, pG) - W.H(cp, G), False
    if t in ('merge', 'pmerge'):
        cp = row['copy']; G = [vec(g) for g in row['G']]
        perm = {c: c for c in range(N)}
        perm.update({int(a): int(b) for a, b in row['perm']})
        tG = []
        for g in G:
            hh = [Fraction(0)] * N
            for c in range(N):
                hh[perm[c]] += g[c]
            tG.append(hh)
        return W.H(cp, tG) - W.H(cp, G), False
    if t in ('bsum', 'batom'):
        return W.S - W.H(row['copy'], [vec(row['f'])]), True
    if t == 'bdiff':
        return W.L - W.H(row['copy'], [vec(row['f'])]), True
    if t == 'dpair':
        D = [v['coords'] for v in verts if v['type'] == 'D'][row['vertex']]
        return W.L - W.H(row['copy'], [e(D[0]), e(D[1])]), False
    if t == 'ident':
        cp = row['copy']; i, j = row['ij']
        gi, gj = (i, j) if cp % 2 == 0 else (j, i)
        return h[(gi, gj)] - W.H(cp, [vec(row['f'])]), False
    if t.startswith('g_'):
        ij = row['ij']
        if t == 'g_h00':
            return -h[(0, 0)], False
        if t == 'g_h11':
            return W.S - h[(1, 1)], True
        i, j = ij
        return {'g_nonneg': lambda: h[(i, j)], 'g_monox': lambda: h[(i + 1, j)] - h[(i, j)],
                'g_monoy': lambda: h[(i, j + 1)] - h[(i, j)],
                'g_concx': lambda: 2 * h[(i + 1, j)] - h[(i, j)] - h[(i + 2, j)],
                'g_concy': lambda: 2 * h[(i, j + 1)] - h[(i, j)] - h[(i, j + 2)],
                'g_link': lambda: h[(i + 1, j)] + h[(i, j + 1)] - h[(i, j)] - W.L}[t](), True
    if t == 'share':
        cpy = row['copy']
        G = [vec(g) for g in row['G']]
        Dc = [v['coords'] for v in verts if v['type'] == 'D']
        pG = []
        for g in G:
            h = list(g)
            if cpy % 2 == 1:
                for (x, y) in Dc:
                    h[x], h[y] = -g[y], -g[x]
            pG.append(h)
        return W.H(0, pG) - W.H(cpy, G), False
    if t == 'xshare':
        G = [vec(g) for g in row['G']]
        mp = {int(a): int(b) for a, b in row['map']}
        pG = []
        for g in G:
            hh = [Fraction(0)] * N
            for c, a in enumerate(g):
                if a:
                    hh[mp[c]] -= a
            pG.append(hh)
        return W.H(0, pG) - W.H(1, G), False
    if t == 'rshare':
        G = [vec(g) for g in row['G']]
        Dc = [v['coords'] for v in verts if v['type'] == 'D']
        wm = {int(a): int(b) for a, b in row.get('wmap', [])}
        pG = []
        for g in G:
            h = [Fraction(0)] * N
            for (x, y) in Dc:
                h[x], h[y] = -g[y], -g[x]
            for a, b in wm.items():
                h[b] -= g[a]
            pG.append(h)
        return W.H(0, pG) - W.H(1, G), False
    if t.startswith('sg_'):
        add4 = lambda tt, dd, m=1: tuple(int(x) + m * int(y) for x, y in zip(tt, dd))
        if t == 'sg_h':
            a, b = row['ab']
            return h[(a, b)] - W.sg((a, 0, b, 0)), False
        if t == 'sg_nonneg':
            return W.sg(row['t']), True
        if t == 'sg_mono':
            return W.sg(add4(row['t'], row['d'])) - W.sg(row['t']), True
        if t == 'sg_conc':
            return 2 * W.sg(add4(row['t'], row['d'])) - W.sg(row['t']) - W.sg(add4(row['t'], row['d'], 2)), True
        if t == 'sg_link':
            dx = tuple(row['dx']); dy = (0, 0, 1, 0) if dx == (1, 0, 0, 0) else (0, 0, 0, 1)
            return W.sg(add4(row['t'], dx)) + W.sg(add4(row['t'], dy)) - W.sg(row['t']) - W.L, True
        if t == 'sg_diff':
            return W.L - W.sg((1, 0, 0, 1)), True
        if t == 'sg_ident':
            return W.sg(row['t']) - W.H(row['copy'], [vec(row['f'])]), False
    if t.startswith('mg_') or t == 'mgident':
        cp = row['copy']; fam = tuple(row['fam']); i, j = row['ij']
        g = lambda a, b: W.mgs[cp % 2][(fam, a, b)]
        hc = lambda a, b: W.grids[cp % 2][(a, b)]
        if t == 'mg_nonneg':
            return g(i, j), True
        if t == 'mg_monox':
            return g(i + 1, j) - g(i, j), True
        if t == 'mg_monoy':
            return g(i, j + 1) - g(i, j), True
        if t == 'mg_concx':
            return 2 * g(i + 1, j) - g(i, j) - g(i + 2, j), True
        if t == 'mg_concy':
            return 2 * g(i, j + 1) - g(i, j) - g(i, j + 2), True
        if t == 'mg_geh':
            return g(i, j) - hc(i, j), True
        if t == 'mg_le1':
            return hc(i + 1, j) + hc(0, 1) - g(i, j), True
        if t == 'mg_ge1':
            return g(i, j) + hc(0, 1) - hc(i + 1, j), True
        if t == 'mg_le2':
            return hc(i, j + 1) + hc(1, 0) - g(i, j), True
        if t == 'mg_ge2':
            return g(i, j) + hc(1, 0) - hc(i, j + 1), True
        if t == 'mgident':
            return g(i, j) - W.H(cp, [vec(row['f'])]), False
    if t in ('matus4', 'five'):
        cp = row['copy']
        V = [[vec(g) for g in gl] for gl in row['vars']]

        def Hj(*idx):
            gens = []
            for k in idx:
                gens += V[k]
            return W.H(cp, gens)

        def I(p, q, r=None):
            if r is None:
                return Hj(p) + Hj(q) - Hj(p, q)
            return Hj(p, r) + Hj(q, r) - Hj(p, q, r) - Hj(r)
        a, b, c, d = 0, 1, 2, 3
        ing = lambda x, y, z, u: -I(x, y) + I(x, y, z) + I(x, y, u) + I(z, u)
        if t == 'matus4':
            s = row['s']
            return I(b, c, a) + s * ing(a, b, c, d) + s * (s + 1) / 2 * (I(a, c, b) + I(a, b, c)), True
        z = 4; k = row['k']; kk = k * (k - 1) / 2
        Ig = ing(a, b, c, d) if row['variant'] == 'abcd' else ing(a, c, b, d)
        if row['fam'] == 'M':
            return I(b, z, a) + k * (Ig + I(a, z, b) + I(a, b, z)) + kk * (I(a, c, b) + I(a, b, c)), True
        return I(a, b, z) + k * (Ig + I(a, z, b) + I(b, z, a)) + kk * (I(a, c, b) + I(b, c, a)), True
    raise ValueError(t)


def run(C, X, Y):
    M = C['grid_depth']
    lam = float(Fraction(C['claimed_lambda']))
    cfgs = C['configs'] if 'configs' in C else [C['config']]
    worlds = [World(X, Y, M, sorted(cf['vertices'], key=lambda v: min(v['coords'])), cf['coords']) for cf in cfgs]
    W = MultiWorld(worlds)
    C = dict(C)
    C['config'] = cfgs[0]
    wi, we, tot = 0.0, 0.0, 0.0
    for row in C['rows']:
        v, ineq = row_value(W, row, C['config']['vertices'])
        m = float(Fraction(row['mult']))
        tot += m * v
        if ineq:
            wi = min(wi, v)
        else:
            we = max(we, abs(v))
    print(f"X={sorted(X)} Y={sorted(Y)} L/S={W.L/W.S:.4f}  min ineq row {wi:.2e}  max|eq row| {we:.2e}  "
          f"sum mult*R = {tot:.6f} vs lambda S - L = {lam*W.S - W.L:.6f}", flush=True)
    return wi, we, tot - (lam * W.S - W.L)


if __name__ == '__main__':
    C = json.load(open(sys.argv[1]))
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    rng = random.Random(int(sys.argv[3]) if len(sys.argv) > 3 else 1)
    sets = [([0, 1, 3], [0, 1, 3]), ([0, 1, 3, 7], [0, 1, 3, 7]), ([0, 1, 3], [0, 2, 3]), ([0, 2, 3, 4, 7], [0, 1, 5])]
    for t in range(trials):
        sets.append((rng.sample(range(10), rng.randint(2, 4)), rng.sample(range(10), rng.randint(2, 4))))
    for X, Y in sets:
        run(C, X, Y)
