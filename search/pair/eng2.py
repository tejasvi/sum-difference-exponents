"""Entropy-LP engine for the two-set exponent: |X - Y| <= |X + Y|^lambda (finite X, Y in Z).
Feeds GGSTW 6.44 (Tao 3a) through Kleinwaks' transfer C_3a <= 2 - 1/lambda.

Model.  X, Y finite subsets of Z; L = log|X-Y|, S = log|X+Y| (normalized S = 1).  Atoms are X-valued or
Y-valued random variables.  Vertex types:
  'D'   pair (x, y) uniform on Gamma in X x Y with one pair per difference: x - y determines (x, y), H = L;
  'UX'  uniform on X;  'UY' uniform on Y;
  'S'   pair (x, y) uniform on Gamma+ in X x Y with one pair per sum: x + y determines (x, y), H = S;
  'PX', 'PY'  single coordinates copied out of a vertex.
Steps: fresh(t); copy(atoms, V) (copy lemma, as in eng643); rep(f, 'D'|'S') (Gamma/Gamma+-representative of
an (X-Y)- or (X+Y)-valued form, new atoms (x', y'), function of f).
Support facts: for an X-atom form x and a Y-atom form y (any coupling): H(x + y) <= S, H(x - y) <= L;
H(x) <= log|X| <= S, H(y) <= log|Y| <= S (|X|, |Y| <= |X+Y|); uniform forms: H(U_X) = log|X| >= H(x).
Grid (Kleinwaks): h(i,j) = H(mu^{*i} * nu^{*j}) for the marginals mu, nu of Gamma; rows (G1) concavity,
(G2) monotone >= 0, (G3) L + h(i,j) <= h(i+1,j) + h(i,j+1), (G4) h(1,1) <= S, up to depth M; grid forms of
mutually independent D-vertices (sums of x's and y's, at most one coordinate per vertex) are identified with
h(i,j).  Reflection: the pair (-Y, -X) with Gamma' = {(-y,-x)} has the same L, S and grid h^T; option
`reflect` adds a second copy of the configuration LP identified with h^T.
"""
import sys, time, itertools
from fractions import Fraction
import numpy as np
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import eng643
from eng643 import (prim, int_nullspace, rank_q, unit, vlin, Solver, rref_add, reduce_all, UF, merge_gens,
                    sub_system_merges, shannon_arrays, solve_lp, IPM, IPMX, P)


class Config2(eng643.Config):
    def __init__(self):
        super().__init__()
        self.color = []          # per coordinate: 'X' or 'Y'
        self.sp = dict(atomX=[], atomY=[], atomW=[], unifX=[], unifY=[], dpair=[], dinj=[], spair=[], sinj=[],
                       sumXY=[], diffXY=[])
        self.indepD = []         # D vertices created independent of everything before (fresh / V = [] copy)
        self.Wpar = {}           # W vertex -> (i, j): an independent variable with law mu^{*i} * nu^{*j}

    def _new_vertex(self, t, k, colors=None):
        v = len(self.vtype)
        cs = list(range(self.N, self.N + k))
        self.N += k
        self.vtype.append(t)
        self.vatoms.append(cs)
        self.atom_v += [v] * k
        self.rels = [list(r) + [0] * k for r in self.rels]
        if colors is None:
            colors = {'D': 'XY', 'S': 'XY', 'UX': 'X', 'UY': 'Y', 'PX': 'X', 'PY': 'Y', 'RD': 'XY', 'RS': 'XY',
                      'W': 'W'}[t]
        for c, col in zip(cs, colors):
            self.color.append(col)
            self.sp['atom' + col].append(unit(self.N, c))
        if t == 'UX':
            self.sp['unifX'].append(unit(self.N, cs[0]))
        if t == 'UY':
            self.sp['unifY'].append(unit(self.N, cs[0]))
        if t == 'D':
            self.sp['dpair'].append((unit(self.N, cs[0]), unit(self.N, cs[1])))
        if t == 'S':
            self.sp['spair'].append((unit(self.N, cs[0]), unit(self.N, cs[1])))
        return v

    def fresh(self, t, wij=None, wsupport=False):
        k = 2 if t in ('D', 'S') else 1
        v = self._new_vertex(t, k)
        self.steps.append(dict(kind='fresh', type=t, v=v, new=list(self.vatoms[v])))
        if t == 'D':
            self.indepD.append(v)
        if t == 'W':
            self.Wpar[v] = tuple(wij)
            # a W with law mu (resp. nu) takes values in X (resp. Y): optionally give it the support rows of an atom
            if wsupport and tuple(wij) == (1, 0):
                self.sp['atomX'].append(unit(self.N, self.vatoms[v][0]))
            if wsupport and tuple(wij) == (0, 1):
                self.sp['atomY'].append(unit(self.N, self.vatoms[v][0]))
        return v

    def copy(self, atoms, V, propagate=True):
        B = self.basisL()
        d = len(B)
        Vc = [self.coords(B, f) for f in V]
        W = self.closure_coords(Vc, B)
        Ucols = [self.coords(B, unit(self.N, c)) for c in atoms]
        Nrows = int_nullspace(W, d) if W else [tuple(1 if i == j else 0 for j in range(d)) for i in range(d)]
        if len(Nrows) == 0:
            alphas = [tuple(1 if i == j else 0 for j in range(len(atoms))) for i in range(len(atoms))]
        else:
            MT = [[sum(x * y for x, y in zip(Ucols[a], Nrows[k])) for a in range(len(atoms))]
                  for k in range(len(Nrows))]
            alphas = int_nullspace(MT, len(atoms))
        Vp = [self.pad(f) for f in V]
        groups = []
        for i, c in enumerate(atoms):
            v = self.atom_v[c]
            for g in groups:
                if g[0] == v:
                    g[1].append(i)
                    break
            else:
                groups.append([v, [i]])
        new = [None] * len(atoms)
        newv = []
        for v, pos in groups:
            t = self.vtype[v]
            if t in ('D', 'S') and len(pos) == 2:
                orig = self.vatoms[v]
                if atoms[pos[0]] == orig[0] and atoms[pos[1]] == orig[1]:
                    nv = self._new_vertex(t, 2)
                    new[pos[0]], new[pos[1]] = self.vatoms[nv]
                    newv.append(nv)
                    if not V:
                        self.indepD.append(nv) if t == 'D' and len(atoms) == 2 else None
                    continue
                if atoms[pos[0]] == orig[1] and atoms[pos[1]] == orig[0]:
                    nv = self._new_vertex(t, 2)
                    new[pos[1]], new[pos[0]] = self.vatoms[nv]
                    newv.append(nv)
                    if not V:
                        self.indepD.append(nv) if t == 'D' and len(atoms) == 2 else None
                    continue
            for i in pos:
                col = self.color[atoms[i]]
                nt = t if t in ('UX', 'UY') else 'P' + col
                nv = self._new_vertex(nt, 1)
                new[i] = self.vatoms[nv][0]
                newv.append(nv)
        newrels = []
        for al in alphas:
            r = [0] * self.N
            for i, c in enumerate(atoms):
                r[c] -= al[i]
                r[new[i]] += al[i]
            if any(r):
                newrels.append(r)
        self.rels = [list(r) + [0] * (self.N - len(r)) for r in self.rels] + newrels
        self.steps.append(dict(kind='copy', atoms=list(atoms), V=Vp, new=list(new), newv=newv))
        if propagate:
            self.propagate([len(self.steps) - 1])
        return new

    def rep(self, f, kind='D'):
        f = self.pad(f)
        v = self._new_vertex('R' + kind, 2)
        cs = self.vatoms[v]
        fr = [Fraction(x) for x in f] + [Fraction(0), Fraction(0)]
        rel = [-x for x in fr]
        rel[cs[0]] += 1
        rel[cs[1]] += (-1 if kind == 'D' else 1)
        den = 1
        for x in rel:
            den = den * x.denominator // eng643.gcd(den, x.denominator)
        self.rels.append([int(x * den) for x in rel])
        a, b = unit(self.N, cs[0]), unit(self.N, cs[1])
        self.sp['dinj' if kind == 'D' else 'sinj'].append((a, b))
        self.steps.append(dict(kind='rep', type=kind, f=fr[:-2], new=cs))
        return cs

    def inj_forms(self):
        out = []
        for a, b in self.sp['dpair'] + self.sp['dinj']:
            out.append((vlin((1, a), (-1, b)), a, b))
        for a, b in self.sp['spair'] + self.sp['sinj']:
            out.append((vlin((1, a), (1, b)), a, b))
        return out

    def propagate(self, steps=None, max_rounds=3):
        if steps is None:
            steps = [t for t, st in enumerate(self.steps) if st['kind'] == 'copy']
        for _ in range(max_rounds):
            B = self.basisL()
            changed = False
            for t in steps:
                if self.steps[t]['kind'] != 'copy':
                    continue
                for kind in ('atomX', 'atomY', 'unifX', 'unifY', 'sumXY', 'diffXY'):
                    lst = self.sp[kind]
                    keys = set(tuple(self.coords(B, f)) for f in lst)
                    for im in self.step_images(t, B, lst):
                        if im is None or not any(im):
                            continue
                        k = tuple(self.coords(B, im))
                        if k not in keys:
                            keys.add(k)
                            lst.append(im)
                            changed = True
                for kind in ('dpair', 'dinj', 'spair', 'sinj'):
                    lst = self.sp[kind]
                    keys = set((tuple(self.coords(B, a)), tuple(self.coords(B, b))) for a, b in lst)
                    ia = self.step_images(t, B, [a for a, b in lst])
                    ib = self.step_images(t, B, [b for a, b in lst])
                    for a2, b2 in zip(ia, ib):
                        if a2 is None or b2 is None:
                            continue
                        k = (tuple(self.coords(B, a2)), tuple(self.coords(B, b2)))
                        if k not in keys:
                            keys.add(k)
                            lst.append((a2, b2))
                            changed = True
            if not changed:
                return

    def describe(self):
        s = " ".join(f"{t}{v}:{self.vatoms[v]}" for v, t in enumerate(self.vtype))
        return s + f" | X-atoms {len(self.sp['atomX'])} Y-atoms {len(self.sp['atomY'])} indepD {self.indepD}"


class Lattice2(eng643.Lattice):
    """Ground set: atom forms, pairwise sums/differences of all atom forms (labels sumXY/diffXY for mixed
    pairs; sumXX etc. for same colour), virtual mixed forms, V forms, extras."""

    def __init__(self, cfg, extra=(), verbose=True, max_flats=10 ** 7):
        self.cfg = cfg
        B = cfg.basisL()
        self.B = B
        self.d = len(B)
        E, key2e, labels, amb = [], {}, [], []

        def add(f, lab):
            c = cfg.coords(B, f)
            k = prim(c)
            if all(a == 0 for a in k):
                return None
            if k not in key2e:
                key2e[k] = len(E)
                E.append(k)
                labels.append(set())
                amb.append(cfg.pad(f))
            e = key2e[k]
            labels[e].add(lab)
            return e

        AX, AY = cfg.sp['atomX'], cfg.sp['atomY']
        for f in AX:
            add(f, 'atomX')
        for f in AY:
            add(f, 'atomY')
        allat = [(f, 'X') for f in AX] + [(f, 'Y') for f in AY]
        for i in range(len(allat)):
            for j in range(i + 1, len(allat)):
                (f, ci), (g, cj) = allat[i], allat[j]
                tag = ''.join(sorted(ci + cj))
                if tag == 'XY':
                    if ci == 'X':
                        add(vlin((1, f), (1, g)), 'sumXY')
                        add(vlin((1, f), (-1, g)), 'diffXY')
                    else:
                        add(vlin((1, g), (1, f)), 'sumXY')
                        add(vlin((1, g), (-1, f)), 'diffXY')
                else:
                    add(vlin((1, f), (1, g)), 'sum' + tag)
                    add(vlin((1, f), (-1, g)), 'diff' + tag)
        for f in cfg.sp['atomW']:
            add(f, 'W')
            for g, cg in allat:
                add(vlin((1, f), (1, g)), 'W')
        for f in cfg.sp['sumXY']:
            add(f, 'sumXY')
        for f in cfg.sp['diffXY']:
            add(f, 'diffXY')
        self.unifX_e = [add(f, 'atomX') for f in cfg.sp['unifX']]
        self.unifY_e = [add(f, 'atomY') for f in cfg.sp['unifY']]
        self.dpair_e, self.spair_e, self.inj_e = [], [], []
        for a, b in cfg.sp['dpair']:
            self.dpair_e.append((add(vlin((1, a), (-1, b)), 'diffXY'), add(a, 'atomX'), add(b, 'atomY')))
        for a, b in cfg.sp['spair']:
            self.spair_e.append((add(vlin((1, a), (1, b)), 'sumXY'), add(a, 'atomX'), add(b, 'atomY')))
        for a, b in cfg.sp['dinj']:
            self.inj_e.append((add(vlin((1, a), (-1, b)), 'diffXY'), add(a, 'atomX'), add(b, 'atomY')))
        for a, b in cfg.sp['sinj']:
            self.inj_e.append((add(vlin((1, a), (1, b)), 'sumXY'), add(a, 'atomX'), add(b, 'atomY')))
        for st in cfg.steps:
            if st['kind'] == 'copy':
                for f in st['V']:
                    add(f, 'V')
        for f in extra:
            add(f, 'extra')
        self.coord_e = [add(unit(cfg.N, c), 'atom' + cfg.color[c]) for c in range(cfg.N)]
        self.E, self.labels, self.amb, self.key2e = E, labels, amb, key2e
        self.extra = [cfg.pad(f) for f in extra]
        self.m = len(E)
        self.Emod = np.array([[a % P for a in e] for e in E], dtype=np.int64)
        self.tri = sorted(set(self.dpair_e + self.spair_e + self.inj_e))
        self.enumerate(verbose, max_flats)


def grid_forms(cfg, lat, maxterms=5):
    """Ground forms that are grid forms of the mutually independent D- and W-vertices: list of (e, i, j)."""
    D = cfg.indepD
    Ws = sorted(cfg.Wpar)
    out = []
    xs = [cfg.vatoms[v][0] for v in D]
    ys = [cfg.vatoms[v][1] for v in D]
    n = len(D)
    for assign in itertools.product((0, 1, 2), repeat=n):   # 0 none, 1 x, 2 y
        for wsel in itertools.product((0, 1), repeat=len(Ws)):
            k = sum(1 for a in assign if a) + sum(wsel)
            if k == 0 or k > maxterms:
                continue
            f = [Fraction(0)] * cfg.N
            gi = sum(1 for a in assign if a == 1)
            gj = sum(1 for a in assign if a == 2)
            for v, a in enumerate(assign):
                if a == 1:
                    f[xs[v]] += 1
                elif a == 2:
                    f[ys[v]] += 1
            for w, s_ in zip(Ws, wsel):
                if s_:
                    f[cfg.vatoms[w][0]] += 1
                    gi += cfg.Wpar[w][0]
                    gj += cfg.Wpar[w][1]
            e = lat.form_e(f)
            if e is not None:
                out.append((e, gi, gj))
    return out


def build_lp2(cfg, lat, M=8, verbose=False, use_diff=True, reflect=False, autos=(), extra_rows=None,
              grid=True, no_g3=False):
    """autos: list of coordinate permutations (dict c -> c') that preserve the joint law (e.g. swapping
    independent iid copies); their induced flat maps are merged."""
    import scipy.sparse as sp
    t0 = time.time()
    maps = eng643.all_maps(cfg, lat, False)
    B = lat.B
    for perm in autos:
        src = [cfg.coords(B, unit(cfg.N, c)) for c in range(cfg.N)]
        img = [cfg.coords(B, unit(cfg.N, perm.get(c, c))) for c in range(cfg.N)]
        maps.append((('auto',), merge_gens(lat, src, img, [])))
    merges = []
    for tag, gens in maps:
        for (Fl, G, gF) in sub_system_merges(lat, gens):
            merges.append((tag, Fl, G, gF))
    uf = UF(lat.nflats)
    for (tag, Fl, G, gF) in merges:
        uf.union(Fl, G)
    cls = np.array([uf.find(i) for i in range(lat.nflats)], dtype=np.int64)
    zc = cls[0]
    uniq = np.unique(cls)
    uniq = uniq[uniq != zc]
    pos = {int(c): i for i, c in enumerate(uniq)}
    colof = np.array([pos.get(int(c), -1) for c in cls], dtype=np.int64)
    nflatcol = len(uniq)
    MA, MK, A, Bv, J, K = shannon_arrays(lat)
    ca, ck = colof[MA], colof[MK]
    keep = ca != ck
    mono = np.stack([ca[keep], ck[keep]], 1) if keep.any() else np.zeros((0, 2), dtype=np.int64)
    if len(mono):
        mono = np.unique(mono, axis=0)
    p = np.sort(np.stack([colof[A], colof[Bv]], 1), 1)
    q = np.sort(np.stack([colof[J], colof[K]], 1), 1)
    rowsP, rowsQ = p.copy(), q.copy()
    for i in range(2):
        for j in range(2):
            mt = (rowsP[:, i] == rowsQ[:, j]) & (rowsP[:, i] != -2)
            rowsP[mt, i] = -2
            rowsQ[mt, j] = -2
    key = np.concatenate([np.sort(rowsP, 1), np.sort(rowsQ, 1)], 1)
    nontriv = ~np.all(np.isin(key, [-1, -2]), axis=1)
    key = key[nontriv]
    if len(key):
        key = np.unique(key, axis=0)
    # columns: [flat cols (copy 1)] [flat cols (reflected copy, if reflect)] [grid h(i,j)] [L]
    ncopies = 2 if reflect else 1
    gidx = {}
    for i in range(M + 1):
        for j in range(M + 1):
            gidx[(i, j)] = ncopies * nflatcol + len(gidx)
    Lcol = ncopies * nflatcol + len(gidx)
    ncol = Lcol + 1
    ri, rj, rv, lo, hi = [], [], [], [], []
    r = 0
    INF = np.inf

    def addrow(dct, l, h):
        nonlocal r
        d = {}
        for c, a in dct:
            if c is None or c < 0:
                continue
            d[c] = d.get(c, 0) + a
        d = {c: a for c, a in d.items() if a != 0}
        if not d:
            if l <= 0 <= h:
                return False
            raise RuntimeError("infeasible constant row")
        ri.append(np.full(len(d), r))
        rj.append(np.array(list(d.keys()), dtype=np.int64))
        rv.append(np.array(list(d.values()), dtype=float))
        lo.append(l)
        hi.append(h)
        r += 1
        return True

    ci = eng643.ci_rows(cfg, lat)
    x0, y0 = lat.coord_e[0], lat.coord_e[1]
    obj_f = lat.cl_ids([x0, y0])
    sX = int(lat.nxt[0, lat.unifX_e[0]]) if lat.unifX_e else None
    sY = int(lat.nxt[0, lat.unifY_e[0]]) if lat.unifY_e else None
    gf = grid_forms(cfg, lat) if grid else []
    for cp in range(ncopies):
        off = cp * nflatcol

        def col(f):
            c = colof[f]
            return None if c < 0 else c + off
        # Shannon
        for a, k in mono:
            addrow([(a + off if a >= 0 else None, 1), (k + off if k >= 0 else None, -1)], 0.0, INF)
        for row in key:
            addrow([(row[0] + off if row[0] >= 0 else None, 1), (row[1] + off if row[1] >= 0 else None, 1),
                    (row[2] + off if row[2] >= 0 else None, -1), (row[3] + off if row[3] >= 0 else None, -1)],
                   0.0, INF)
        for t, rw in ci:
            addrow([(col(f), a) for f, a in rw], 0.0, 0.0)
        # objective identification: H(x0,y0) = L
        addrow([(col(obj_f), 1), (Lcol, -1)], 0.0, 0.0)
        for e, labs in enumerate(lat.labels):
            fl = int(lat.nxt[0, e])
            if 'sumXY' in labs:
                addrow([(col(fl), 1)], -INF, 1.0)
            if 'diffXY' in labs and use_diff:
                addrow([(col(fl), 1), (Lcol, -1)], -INF, 0.0)
            if 'atomX' in labs:
                addrow([(col(fl), 1)], -INF, 1.0)
                if sX is not None:
                    addrow([(col(fl), 1), (col(sX), -1)], -INF, 0.0)
            if 'atomY' in labs:
                addrow([(col(fl), 1)], -INF, 1.0)
                if sY is not None:
                    addrow([(col(fl), 1), (col(sY), -1)], -INF, 0.0)
        for e in lat.unifX_e:
            addrow([(col(int(lat.nxt[0, e])), 1), (col(sX), -1)], 0.0, 0.0)
        for e in lat.unifY_e:
            addrow([(col(int(lat.nxt[0, e])), 1), (col(sY), -1)], 0.0, 0.0)
        for (de, xe, ye) in lat.dpair_e:
            addrow([(col(lat.cl_ids([xe, ye])), 1), (Lcol, -1)], 0.0, 0.0)
        for (se, xe, ye) in lat.spair_e:
            addrow([(col(lat.cl_ids([xe, ye])), 1)], 1.0, 1.0)
        # grid identifications (copy 0: h(i,j); reflected copy: h(j,i))
        for (e, i, j) in gf:
            gi, gj = (i, j) if cp == 0 else (j, i)
            if (gi, gj) in gidx:
                addrow([(col(int(lat.nxt[0, e])), 1), (gidx[(gi, gj)], -1)], 0.0, 0.0)
    ngridrows = 0
    if grid:
        r0 = r
        Hh = lambda i, j: gidx.get((i, j))
        for (i, j), c in gidx.items():
            if i == 0 and j == 0:
                addrow([(c, 1)], 0.0, 0.0)
            addrow([(c, 1)], 0.0, INF)
            if Hh(i + 1, j) is not None:
                addrow([(Hh(i + 1, j), 1), (c, -1)], 0.0, INF)
            if Hh(i, j + 1) is not None:
                addrow([(Hh(i, j + 1), 1), (c, -1)], 0.0, INF)
            if Hh(i + 2, j) is not None:
                addrow([(Hh(i + 1, j), 2), (c, -1), (Hh(i + 2, j), -1)], 0.0, INF)
            if Hh(i, j + 2) is not None:
                addrow([(Hh(i, j + 1), 2), (c, -1), (Hh(i, j + 2), -1)], 0.0, INF)
            if not no_g3 and Hh(i + 1, j) is not None and Hh(i, j + 1) is not None:
                addrow([(Hh(i + 1, j), 1), (Hh(i, j + 1), 1), (c, -1), (Lcol, -1)], 0.0, INF)
        addrow([(Hh(1, 1), 1)], -INF, 1.0)
        ngridrows = r - r0
    if extra_rows:
        for (dct, l, h) in extra_rows(lat, colof, gidx, Lcol):
            addrow(list(dct.items()), l, h)
    Amat = sp.csr_matrix((np.concatenate(rv), (np.concatenate(ri), np.concatenate(rj))), shape=(r, ncol))
    if verbose:
        print(f"  LP2: {ncol} cols ({nflatcol} flat cols x{ncopies}, grid {len(gidx)}), {r} rows, merges "
              f"{len(merges)}, grid forms {len(gf)}, grid rows {ngridrows}, {time.time()-t0:.2f}s", flush=True)
    return dict(A=Amat, lo=np.array(lo), hi=np.array(hi), ncol=ncol, obj_col=Lcol, colof=colof, gidx=gidx,
                merges=merges, gf=gf, nflatcol=nflatcol)


def evaluate2(cfg, extra=(), verbose=False, max_flats=300000, opts=IPM, **kw):
    lat = Lattice2(cfg, extra=extra, verbose=verbose, max_flats=max_flats)
    L = build_lp2(cfg, lat, verbose=verbose, **kw)
    S = solve_lp(L, opts=opts)
    return S, L, lat


def F(cfg, dct):
    f = [Fraction(0)] * cfg.N
    for c, a in dct.items():
        f[c] = Fraction(a)
    return f
