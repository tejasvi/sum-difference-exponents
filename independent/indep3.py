#!/usr/bin/env python3
"""Audit checker for two-set exponent certificates (the format read by checker/check3.py), written from the mathematics:
nothing is imported from the search programs or from checker/check3.py.

Usage: python -I indep3.py CERT.json [--no-inj] [--strict-ci]

Mathematical setting (my own statement of it).
  X, Y finite nonempty subsets of Z; Gamma subset of X x Y with exactly one pair per element of X - Y;
  (X1, Y1) uniform on Gamma; L = log|X - Y| = H(X1, Y1); S = log|X + Y|; mu, nu = laws of X1, Y1;
  h(i, j) = H(mu^{*i} * nu^{*j}) (h(0,0) = 0).
  Configuration ("copy 0"): mutually independent vertices; a D vertex is a pair (x_k, y_k) with the law of (X1, Y1);
  a W vertex is one coordinate w with law mu^{*a} * nu^{*b}.  "Copy 1" is the same configuration built from the
  reflected pair (-Y, -X) with Gamma' = {(-y, -x)}: same L and S, and its grid is h'(i, j) = h(j, i).
  For a list G of linear forms (vectors over Q indexed by the coordinates), H(G) is the joint entropy; it depends
  only on cl(G) = smallest subspace containing G and closed under "x_k - y_k in it => x_k, y_k in it" (values are
  integers, so a rational multiple of a determined integer form is determined; and on Gamma the difference
  determines the pair).  Flats are keyed by the canonical RREF of cl(G) (python-flint), separately per copy.
Rows (inequality rows need mult >= 0):
  sub: I(i;j|K) >= 0      mono: H(K,i) - H(K) >= 0
  ci: H(old,new) - H(old) - H(new) = 0 where new = all coordinates of one vertex and old = all coordinates of a set
      of other vertices (mutual independence; --strict-ci additionally requires old = all earlier vertices)
  merge: H(tau G) - H(G) = 0, tau a permutation of the D vertices (pairs to pairs, x to x, y to y) combined with a
      permutation of the W vertices among W vertices of the same law (all vertices mutually independent)
  bsum: S - H(x + y) >= 0 (x + y in X + Y)        bdiff: L - H(x - y) >= 0 (in X - Y)
  batom: S - H(x) >= 0 or S - H(y) >= 0 (|X|, |Y| <= |X + Y|)
      where x is an X-valued coordinate (x_k, or a W with law mu) and y a Y-valued one (y_k, or a W with law nu)
  dpair: L - H(x_k, y_k) = 0
  ident: h(i, j) - H(f) = 0 (copy 0) or h(j, i) - H(f) = 0 (copy 1), f a sum with coefficients 1 of coordinates from
      distinct vertices, at most one coordinate per D vertex; i, j computed here from the vertex laws
  grid: g_h00 h(0,0) = 0; g_nonneg h >= 0; g_monox/g_monoy monotone; g_concx/g_concy concave (Madiman); g_link
      h(i+1,j) + h(i,j+1) - h(i,j) - L >= 0 (coupled Ruzsa, Kleinwaks Lemma 3.2); g_h11 S - h(1,1) >= 0
  rshare: H_0(phi G) - H_1(G) = 0 for G supported on D coordinates, phi: x_k -> -y_k, y_k -> -x_k (equality of laws)
  pmerge: H(tau G) - H(G) = 0, tau a coordinate permutation sending the touched part of each touched vertex into one
      vertex, distinct vertices to distinct vertices, with equal laws of the touched parts (see the code comment)
  xshare: H_0(tau G) - H_1(G) = 0, tau = minus a map from copy-1 coordinates to copy-0 coordinates sending the touched
      part of each copy-1 vertex into one copy-0 vertex, distinct to distinct, with transposed laws (see the code comment)
  matus4 (Matus 2007, DFZ arXiv:1104.3602 eq. (80)): M_s(a,b,c,d) = I(b;c|a) + s[abcd] + C(s+1,2)(I(a;c|b) + I(a;b|c)),
      integer 1 <= s <= 1000 (validity proved independently by ../matus_lp.py and ../matus_param.py)
  five (Csirmaz-Csirmaz, as stated in Kleinwaks Sec. 3.4): with Ingleton [abcd] = -I(a;b)+I(a;b|c)+I(a;b|d)+I(c;d)
      (variant 'acbd' uses [acbd] instead),
      M_k = I(b;z|a) + k([.] + I(a;z|b) + I(a;b|z)) + C(k,2)(I(a;c|b) + I(a;b|c))
      C_k = I(a;b|z) + k([.] + I(a;z|b) + I(b;z|a)) + C(k,2)(I(a;c|b) + I(b;c|a)),
      integer 1 <= k <= 300 (validity proved independently by five_lp.py, five_param.py); variables are joint variables
Identity: sum mult * R == lambda * S - L exactly; then L <= lambda S.
"""
import json
import sys
from collections import defaultdict
from fractions import Fraction

import flint


def fq(x):
    return flint.fmpq(x.numerator, x.denominator)


class Cfg:
    def __init__(self, cfg, inj=True):
        self.n = int(cfg['coords'])
        self.D, self.W = [], []
        cover = []
        for v in cfg['vertices']:
            cs = [int(c) for c in v['coords']]
            cover += cs
            if v['type'] == 'D':
                if len(cs) != 2:
                    raise ValueError('D vertex needs 2 coordinates')
                self.D.append(tuple(cs))
            elif v['type'] == 'W':
                a, b = (int(t) for t in v['ij'])
                if len(cs) != 1 or a < 0 or b < 0:
                    raise ValueError('bad W vertex')
                self.W.append((cs[0], a, b))
            else:
                raise ValueError('unknown vertex type')
        if sorted(cover) != list(range(self.n)):
            raise ValueError('vertices do not partition the coordinates')
        self.vertices = [frozenset(d) for d in self.D] + [frozenset([w]) for w, _, _ in self.W]
        self.inj = inj
        self.cache = {}

    def e(self, c):
        v = [Fraction(0)] * self.n
        v[c] = Fraction(1)
        return v

    def rref(self, vecs):
        vecs = [v for v in vecs if any(a != 0 for a in v)]
        if not vecs:
            return ()
        M = flint.fmpq_mat(len(vecs), self.n, [fq(a) for v in vecs for a in v])
        R, r = M.rref()
        return tuple(tuple((int(R[i, j].p), int(R[i, j].q)) for j in range(self.n)) for i in range(r))

    def contains(self, key, v):
        if not any(a != 0 for a in v):
            return True
        rows = [[Fraction(p, q) for p, q in row] for row in key]
        return len(self.rref(rows + [v])) == len(key)

    def closure(self, gens):
        k0 = tuple(tuple(g) for g in gens)
        if k0 in self.cache:
            return self.cache[k0]
        key = self.rref([list(g) for g in gens])
        while self.inj:
            grew = False
            for x, y in self.D:
                d = [Fraction(0)] * self.n
                d[x], d[y] = Fraction(1), Fraction(-1)
                if key and self.contains(key, d):
                    for c in (x, y):
                        if not self.contains(key, self.e(c)):
                            key = self.rref([[Fraction(p, q) for p, q in row] for row in key] + [self.e(c)])
                            grew = True
            if not grew:
                break
        self.cache[k0] = key
        return key


def check(C, inj=True, strict_ci=False):
    cfg = Cfg(C['config'], inj=inj)
    M = int(C['grid_depth'])
    lam = Fraction(C['claimed_lambda'])
    n = cfg.n
    tot = defaultdict(Fraction)

    def vec(f):
        v = [Fraction(a) for a in f]
        if len(v) != n:
            raise ValueError('form length')
        return v

    def H(cp, gens, c):
        key = cfg.closure(gens)
        if key:
            tot[('H', cp, key)] += c

    def hh(i, j, c):
        if not (0 <= i <= M and 0 <= j <= M):
            raise ValueError(f'grid index ({i},{j}) outside depth {M}')
        if (i, j) != (0, 0):
            tot[('h', i, j)] += c
        # h(0,0) = 0 identically (law delta_0); keep it as 0

    def support_of(f):
        return [c for c in range(n) if f[c] != 0]

    # X-valued coordinates: x_k of D vertices and W vertices with law mu (values in X; in copy 1, in X' = -Y);
    # Y-valued: y_k and W vertices with law nu.  Then x + y lies in X + Y and x - y in X - Y.
    XV = {x for x, _ in cfg.D} | {w for w, a_, b_ in cfg.W if (a_, b_) == (1, 0)}
    YV = {y for _, y in cfg.D} | {w for w, a_, b_ in cfg.W if (a_, b_) == (0, 1)}

    def is_xy(f, sign):
        nz = support_of(f)
        if len(nz) != 2:
            return False
        xs, ys = XV, YV
        for a, b in ((nz[0], nz[1]), (nz[1], nz[0])):
            if a in xs and b in ys and abs(f[a]) == 1 and f[b] == sign * f[a]:
                return True
        return False

    for r in C['rows']:
        t = r['type']
        m = Fraction(r['mult'])
        ineq = t in ('sub', 'mono', 'bsum', 'bdiff', 'batom') or t in ('g_nonneg', 'g_monox', 'g_monoy', 'g_concx',
                                                                       'g_concy', 'g_link', 'g_h11')
        if ineq and m < 0:
            return False, f'negative multiplier on inequality row {t}'
        cp = int(r.get('copy', 0))
        if cp not in (0, 1):
            return False, 'copy must be 0 or 1'
        if t in ('sub', 'mono'):
            K = [vec(g) for g in r['K']]
            i = vec(r['i'])
            H(cp, K + [i], m)
            H(cp, K, -m)
            if t == 'sub':
                j = vec(r['j'])
                H(cp, K + [j], m)
                H(cp, K + [i, j], -m)
        elif t == 'ci':
            new = frozenset(int(c) for c in r['new'])
            old = frozenset(int(c) for c in r['old'])
            if new not in cfg.vertices:
                return False, 'ci: new is not one vertex'
            if new & old:
                return False, 'ci: old meets new'
            olds = [v for v in cfg.vertices if v <= old]
            covered = frozenset().union(*olds) if olds else frozenset()
            if covered != old:
                return False, 'ci: old is not a union of vertices'
            if strict_ci:
                idx = cfg.vertices.index(new)
                if old != frozenset().union(*cfg.vertices[:idx]):
                    return False, 'ci: old is not all earlier vertices'
            H(cp, [cfg.e(c) for c in sorted(old | new)], m)
            H(cp, [cfg.e(c) for c in sorted(old)], -m)
            H(cp, [cfg.e(c) for c in sorted(new)], -m)
        elif t == 'merge':
            perm = {c: c for c in range(n)}
            for a, b in r['perm']:
                perm[int(a)] = int(b)
            if sorted(perm.values()) != list(range(n)):
                return False, 'merge: not a permutation'
            dset = set(cfg.D)
            for x, y in cfg.D:
                if (perm[x], perm[y]) not in dset:
                    return False, 'merge: does not map D vertices to D vertices'
            wlaw = {w: (a_, b_) for w, a_, b_ in cfg.W}
            for w, a_, b_ in cfg.W:
                # W vertices are mutually independent, independent of the D's; equal-law W's are iid, so they may
                # be permuted among themselves (together with any permutation of the iid D vertices)
                if perm[w] not in wlaw or wlaw[perm[w]] != (a_, b_):
                    return False, 'merge: maps a W coordinate to a non-W coordinate or to a W of another law'
            G = [vec(g) for g in r['G']]
            tG = []
            for g in G:
                h = [Fraction(0)] * n
                for c in range(n):
                    h[perm[c]] += g[c]
                tG.append(h)
            H(cp, tG, m)
            H(cp, G, -m)
        elif t == 'pmerge':
            # Partial merge (my statement).  The vertices are mutually independent.  Let U = coordinates with a nonzero
            # coefficient in some generator, U_v = U cap (coordinates of vertex v).  If tau sends U_v into ONE vertex
            # t(v) for every touched v, t is injective, and (Z_c)_{c in U_v} has the law of (Z_tau(c))_{c in U_v} for every
            # v, then (Z_c)_{c in U} and (Z_tau(c))_{c in U} are both products of equal laws over distinct independent
            # vertices, so G and tau G have the same joint law and H(G) = H(tau G).  Laws: a D vertex touched in both
            # coordinates has the pair law (X1, Y1): its image must be a D vertex with x -> x, y -> y; a single touched
            # coordinate has type (1,0) (x_k: law mu), (0,1) (y_k: law nu) or (a,b) (W: law mu^{*a} nu^{*b}), and its
            # image must have the same type.  The same holds inside copy 1 with (mu', nu') in place of (mu, nu).
            perm = {c: c for c in range(n)}
            for a, b in r['perm']:
                perm[int(a)] = int(b)
            if sorted(perm.values()) != list(range(n)):
                return False, 'pmerge: not a permutation'
            G = [vec(g) for g in r['G']]
            U = sorted({c for g in G for c in range(n) if g[c] != 0})
            vof, role = {}, {}
            for k, (x, y) in enumerate(cfg.D):
                vof[x], role[x] = ('D', k), 'x'
                vof[y], role[y] = ('D', k), 'y'
            for w, a_, b_ in cfg.W:
                vof[w], role[w] = ('W', w), (a_, b_)
            typ = lambda c: (1, 0) if role[c] == 'x' else ((0, 1) if role[c] == 'y' else role[c])  # noqa: E731
            touched = defaultdict(list)
            for c in U:
                touched[vof[c]].append(c)
            used_targets = set()
            for v, cs in touched.items():
                tv = {vof[perm[c]] for c in cs}
                if len(tv) != 1:
                    return False, 'pmerge: the touched part of a vertex is sent into two vertices'
                tv = tv.pop()
                if tv in used_targets:
                    return False, 'pmerge: two touched vertices are sent into the same vertex'
                used_targets.add(tv)
                if len(cs) == 2:
                    if tv[0] != 'D' or any(role[perm[c]] != role[c] for c in cs):
                        return False, 'pmerge: a fully touched D vertex must go to a D vertex, x to x and y to y'
                elif typ(perm[cs[0]]) != typ(cs[0]):
                    return False, 'pmerge: a single touched coordinate must go to a coordinate of the same law type'
            tG = []
            for g in G:
                h = [Fraction(0)] * n
                for c in range(n):
                    h[perm[c]] += g[c]
                tG.append(h)
            H(cp, tG, m)
            H(cp, G, -m)
        elif t in ('bsum', 'bdiff', 'batom'):
            f = vec(r['f'])
            if t == 'bsum':
                if not is_xy(f, +1):
                    return False, 'bsum: f is not +-(x_k + y_l)'
                tot[('S',)] += m
            elif t == 'bdiff':
                if not is_xy(f, -1):
                    return False, 'bdiff: f is not +-(x_k - y_l)'
                tot[('L',)] += m
            else:
                nz = support_of(f)
                if len(nz) != 1 or abs(f[nz[0]]) != 1 or nz[0] not in (XV | YV):
                    return False, 'batom: f is not a single X- or Y-valued coordinate'
                tot[('S',)] += m
            H(cp, [f], -m)
        elif t == 'dpair':
            x, y = cfg.D[int(r['vertex'])]
            tot[('L',)] += m
            H(cp, [cfg.e(x), cfg.e(y)], -m)
        elif t == 'ident':
            f = vec(r['f'])
            if any(a not in (0, 1) for a in f) or not any(f):
                return False, 'ident: coefficients must be 0/1, form nonzero'
            i = j = 0
            for x, y in cfg.D:
                if f[x] and f[y]:
                    return False, 'ident: both coordinates of one D vertex'
                i += int(f[x] == 1)
                j += int(f[y] == 1)
            for w, a, b in cfg.W:
                if f[w]:
                    i += a
                    j += b
            if [i, j] != [int(t_) for t_ in r['ij']]:
                return False, f"ident: computed ({i},{j}) != claimed {r['ij']}"
            if cp == 1:
                i, j = j, i
            hh(i, j, m)
            H(cp, [f], -m)
        elif t.startswith('g_'):
            ij = r.get('ij', [])
            if t == 'g_h00':
                pass  # h(0,0) = 0 is built in
            elif t == 'g_h11':
                tot[('S',)] += m
                hh(1, 1, -m)
            else:
                i, j = (int(a) for a in ij)
                if t == 'g_nonneg':
                    hh(i, j, m)
                elif t == 'g_monox':
                    hh(i + 1, j, m); hh(i, j, -m)
                elif t == 'g_monoy':
                    hh(i, j + 1, m); hh(i, j, -m)
                elif t == 'g_concx':
                    hh(i + 1, j, 2 * m); hh(i, j, -m); hh(i + 2, j, -m)
                elif t == 'g_concy':
                    hh(i, j + 1, 2 * m); hh(i, j, -m); hh(i, j + 2, -m)
                elif t == 'g_link':
                    hh(i + 1, j, m); hh(i, j + 1, m); hh(i, j, -m)
                    tot[('L',)] -= m
                else:
                    return False, f'unknown grid row {t}'
        elif t == 'xshare':
            # Copy 1 is built from Gamma' = {(-y, -x)}: D'_k ~ (-Y1, -X1), so x'_k ~ mu' = law(-Y1), y'_k ~ nu' = law(-X1),
            # and a copy-1 W of type (a,b) ~ mu'^{*a} nu'^{*b} = law of -(a copy-0 W of type (b,a)).  The vertices of each
            # copy are mutually independent.  If the map sends the touched part of each touched copy-1 vertex into ONE
            # copy-0 vertex, distinct vertices to distinct vertices, and each touched part has the law of its NEGATED image
            # (fully touched D'_k -> D_m with x'_k -> y_m, y'_k -> x_m; one coordinate of type (a,b) -> one of type (b,a),
            # types x: (1,0), y: (0,1), W: its (a,b)), then (Z'_c)_{c in U} ~ (-Z_map(c))_{c in U} (products of equal laws
            # over distinct independent vertices), so H_1(G) = H_0(tau G) with (tau g)_map(c) = -g_c.  Map keys = support.
            G = [vec(g) for g in r['G']]
            mp = {}
            for a, b in r['map']:
                a, b = int(a), int(b)
                if a in mp or not (0 <= b < n):
                    return False, 'xshare: map defines a coordinate twice or maps outside the coordinates'
                mp[a] = b
            U = {c for g in G for c in range(n) if g[c] != 0}
            if set(mp) != U:
                return False, 'xshare: the map must be defined exactly on the support of G'
            vof, role = {}, {}
            for k, (x, y) in enumerate(cfg.D):
                vof[x], role[x] = ('D', k), 'x'
                vof[y], role[y] = ('D', k), 'y'
            for w, a_, b_ in cfg.W:
                vof[w], role[w] = ('W', w), (a_, b_)
            typ = lambda c: (1, 0) if role[c] == 'x' else ((0, 1) if role[c] == 'y' else role[c])  # noqa: E731
            touched = defaultdict(list)
            for c in sorted(U):
                touched[vof[c]].append(c)
            used_targets = set()
            for v, cs in touched.items():
                tv = {vof[mp[c]] for c in cs}
                if len(tv) != 1:
                    return False, 'xshare: the touched part of a copy-1 vertex is sent into two copy-0 vertices'
                tv = tv.pop()
                if tv in used_targets:
                    return False, 'xshare: two copy-1 vertices are sent into the same copy-0 vertex'
                used_targets.add(tv)
                if len(cs) == 2:
                    xk, yk = cfg.D[v[1]]
                    if tv[0] != 'D' or role[mp[xk]] != 'y' or role[mp[yk]] != 'x':
                        return False, 'xshare: a fully touched copy-1 pair must go to (-y_m, -x_m) of one copy-0 D vertex'
                else:
                    a_, b_ = typ(cs[0])
                    if typ(mp[cs[0]]) != (b_, a_):
                        return False, 'xshare: a single coordinate must go to a coordinate of the transposed law type'
            pG = []
            for g in G:
                h_ = [Fraction(0)] * n
                for c in U:
                    h_[mp[c]] -= g[c]
                pG.append(h_)
            H(0, pG, m)
            H(1, G, -m)
        elif t == 'rshare':
            # Copy 1 (built from Gamma' = {(-y,-x)}): D vertices iid uniform on Gamma', and a W vertex of ij (a,b) has law
            # mu'^{*a} nu'^{*b} with mu' = law(-Y1) = refl(nu), nu' = law(-X1) = refl(mu), i.e. the law of -W_b' for a
            # copy-0 W vertex b' of TRANSPOSED ij (b,a).  So if wmap a -> b (a, b W coordinates, b has the transposed law
            # of a, injective), copy 1's (D', W'_a for mapped a) has the joint law of copy 0's ((-y_k,-x_k)_k, (-W_b)):
            # the images are functions of distinct mutually independent copy-0 vertices with the right laws.
            # Hence H_1(G) = H_0(phi G) for G supported on D coordinates and mapped W coordinates, with
            # phi: x_k -> -y_k, y_k -> -x_k, w_a -> -w_b.
            G = [vec(g) for g in r['G']]
            wlaw = {w_: (a_, b_) for w_, a_, b_ in cfg.W}
            wm = {}
            for a_, b_ in r.get('wmap', []):
                a_, b_ = int(a_), int(b_)
                if a_ in wm:
                    return False, 'rshare: wmap maps a coordinate twice'
                wm[a_] = b_
            if len(set(wm.values())) != len(wm):
                return False, 'rshare: wmap not injective'
            for a_, b_ in wm.items():
                if a_ not in wlaw or b_ not in wlaw or wlaw[b_] != (wlaw[a_][1], wlaw[a_][0]):
                    return False, 'rshare: wmap must map a W vertex to a W vertex of the transposed law'
            dco = {c_ for pr in cfg.D for c_ in pr}
            if any(g[c_] != 0 for g in G for c_ in range(n) if c_ not in dco and c_ not in wm):
                return False, 'rshare: generators must be supported on D coordinates and mapped W coordinates'
            pG = []
            for g in G:
                h_ = [Fraction(0)] * n
                for x_, y_ in cfg.D:
                    h_[x_] = -g[y_]
                    h_[y_] = -g[x_]
                for a_, b_ in wm.items():
                    h_[b_] = -g[a_]
                pG.append(h_)
            H(0, pG, m)
            H(1, G, -m)
        elif t in ('matus4', 'five'):
            V = [[vec(g) for g in gl] for gl in r['vars']]

            def J(*ks):
                out = []
                for k_ in ks:
                    out += V[k_]
                return out

            def mi(coef, p, q, rr=None):
                # coef * I(V[p]; V[q] | V[rr])
                zc = J(rr) if rr is not None else []
                H(cp, J(p) + zc, coef)
                H(cp, J(q) + zc, coef)
                H(cp, J(p, q) + zc, -coef)
                H(cp, zc, -coef)

            def ing(coef, A_, B_, C_, D_):
                mi(-coef, A_, B_)
                mi(coef, A_, B_, C_)
                mi(coef, A_, B_, D_)
                mi(coef, C_, D_)
            if m < 0:
                return False, 'negative multiplier on non-Shannon row'
            if t == 'matus4':
                sv = r['s']
                if not isinstance(sv, int) or not (1 <= sv <= 1000) or len(V) != 4:
                    return False, 'matus4: s must be an integer in [1, 1000], 4 variables'
                S_ = Fraction(sv)
                mi(m, 1, 2, 0)
                ing(m * S_, 0, 1, 2, 3)
                mi(m * S_ * (S_ + 1) / 2, 0, 2, 1)
                mi(m * S_ * (S_ + 1) / 2, 0, 1, 2)
            else:
                kv = r['k']
                if not isinstance(kv, int) or not (1 <= kv <= 300) or len(V) != 5:
                    return False, 'five: k must be an integer in [1, 300], 5 variables'
                if r['fam'] not in ('M', 'C') or r['variant'] not in ('abcd', 'acbd'):
                    return False, 'five: bad family or variant'
                K_ = Fraction(kv)
                kk = K_ * (K_ - 1) / 2
                A_, B_, C_, D_, Z_ = 0, 1, 2, 3, 4
                if r['variant'] == 'abcd':
                    ing(m * K_, A_, B_, C_, D_)
                else:
                    ing(m * K_, A_, C_, B_, D_)
                if r['fam'] == 'M':
                    mi(m, B_, Z_, A_); mi(m * K_, A_, Z_, B_); mi(m * K_, A_, B_, Z_)
                    mi(m * kk, A_, C_, B_); mi(m * kk, A_, B_, C_)
                else:
                    mi(m, A_, B_, Z_); mi(m * K_, A_, Z_, B_); mi(m * K_, B_, Z_, A_)
                    mi(m * kk, A_, C_, B_); mi(m * kk, B_, C_, A_)
        else:
            return False, f'row type {t} not supported by this checker'
    target = {('S',): lam, ('L',): Fraction(-1)}
    bad = [k for k in set(tot) | set(target) if tot.get(k, Fraction(0)) != target.get(k, Fraction(0))]
    if bad:
        return False, f'identity fails on {len(bad)} terms, e.g. {[(k[:2], tot.get(k, 0)) for k in bad[:3]]}'
    return True, lam


if __name__ == '__main__':
    args = sys.argv[1:]
    path = [a for a in args if not a.startswith('--')][0]
    C = json.load(open(path))
    ok, info = check(C, inj='--no-inj' not in args, strict_ci='--strict-ci' in args)
    if ok:
        c3a = 2 - 1 / info
        print(f'[audit643] PASS: log|X-Y| <= lambda log|X+Y|, lambda = {info} = {float(info):.12f}; '
              f'C_3a <= 2 - 1/lambda = {c3a} = {float(c3a):.12f}')
        sys.exit(0)
    print(f'[audit643] FAIL: {info}')
    sys.exit(1)
