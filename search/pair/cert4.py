"""Certification from the MERGED LP (flats identified by equal-law merges), much smaller than cert3's tagged LP.
The merged LP's exact dual is turned into an explicit certificate for check3.py:
  * every support row is written with explicit representative flats (any representative is a valid instance);
  * the remaining imbalance inside each merge class is cancelled by explicit merge rows along a spanning tree of the
    actual merge edges (tree flow), so the identity holds flat by flat.
Configurations: mutually independent D/W vertices (fresh or V = [] copies), swap automorphisms of the D copies."""
import sys, time, json
from fractions import Fraction
import numpy as np
import scipy.sparse as sp
import flint
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from eng643 import shannon_arrays, merge_gens, sub_system_merges, unit, solve_lp, IPMX, IPM, UF
import eng643
from eng2 import grid_forms
from ns2 import matus_row, five_row


MG_FAMS = ((1, 1), (1, -1))


class LazyTags:
    """Row tags: the first n_sh rows are Shannon rows stored as arrays (kind 0 = mono (a, k), 1 = sub (a, b, j, k)),
    the remaining rows have explicit tuples."""
    def __init__(self, kind, cp, a, b, j, k, other):
        self.kind, self.cp, self.a, self.b, self.j, self.k = kind, cp, a, b, j, k
        self.n_sh = len(kind)
        self.other = other

    def __len__(self):
        return self.n_sh + len(self.other)

    def __getitem__(self, i):
        i = int(i)
        if i < self.n_sh:
            if self.kind[i] == 0:
                return ('mono', int(self.cp[i]), int(self.a[i]), int(self.k[i]))
            return ('sub', int(self.cp[i]), int(self.a[i]), int(self.b[i]), int(self.j[i]), int(self.k[i]))
        return self.other[i - self.n_sh]

    def __iter__(self):
        for i in range(len(self)):
            yield self[i]


def canon_rows(C, V):
    """Canonical form of rows with up to 4 (column, coefficient) entries: column -1 = absent; equal columns combined,
    zero entries removed, entries sorted by column with absent entries last."""
    C = C.copy(); V = V.copy()
    V[C < 0] = 0
    BIG = np.iinfo(np.int64).max
    for _ in range(3):
        Cs = np.where(V == 0, BIG, C)
        o = np.argsort(Cs, axis=1, kind='stable')
        C = np.take_along_axis(Cs, o, axis=1); V = np.take_along_axis(V, o, axis=1)
        for t in range(C.shape[1] - 1):
            same = (C[:, t] == C[:, t + 1]) & (C[:, t] != BIG)
            V[same, t + 1] += V[same, t]
            V[same, t] = 0
    Cs = np.where(V == 0, BIG, C)
    o = np.argsort(Cs, axis=1, kind='stable')
    C = np.take_along_axis(Cs, o, axis=1); V = np.take_along_axis(V, o, axis=1)
    C[V == 0] = -1
    return C, V


def row_hash(C, V):
    h = np.zeros(C.shape[0], dtype=np.uint64)
    with np.errstate(over='ignore'):
        for t in range(C.shape[1]):
            h = h * np.uint64(1000003) + (C[:, t].astype(np.int64) + 2).astype(np.uint64)
            h = h * np.uint64(0x9E3779B97F4A7C15 & 0xFFFFFFFFFFFFFFFF) + (V[:, t] + 8).astype(np.uint64)
    return h


def sub_system_merges_img(lat, gens):
    """As eng643.sub_system_merges, also returning the image generators: (F, G, gF, gImg)."""
    seen = {0: ()}
    queue = [0]
    while queue:
        F = queue.pop()
        gF = seen[F]
        for gi, (e, e2) in enumerate(gens):
            F2 = int(lat.nxt[F, e])
            if F2 not in seen:
                seen[F2] = gF + (gi,)
                queue.append(F2)
    out = []
    for F, gF in seen.items():
        if F == 0:
            continue
        G = lat.cl_ids([gens[gi][1] for gi in gF])
        if G != F:
            out.append((F, G, [gens[gi][0] for gi in gF], [gens[gi][1] for gi in gF]))
    return out


def cert_vertices(cfg):
    """Certificate vertex list (coordinate order) and map conditional-copy step -> vertex index.
    D: independent copy of (X1, Y1); W: independent, law mu^{*i} nu^{*j}; C: conditional copy of the src
    coordinates given the given forms (single-coordinate atoms only, no induced relations)."""
    vstep = {}
    for t, st in enumerate(cfg.steps):
        if st['kind'] == 'copy' and st['V']:
            for nv in st['newv']:
                vstep[nv] = t
    verts, step_v, done = [], {}, set()
    for v, tp in enumerate(cfg.vtype):
        if v in vstep:
            t = vstep[v]
            if t in done:
                continue
            done.add(t)
            st = cfg.steps[t]
            assert all(cfg.vtype[nv] in ('PX', 'PY') for nv in st['newv']), "conditional copies of single atoms only"
            assert not any(r[c] for r in cfg.rels for c in st['new'] if c < len(r)), "conditional copy with relations"
            step_v[t] = len(verts)
            verts.append(dict(type='C', coords=list(st['new']), src=list(st['atoms']),
                              given=[[str(x) for x in cfg.pad(f)] for f in st['V']]))
        elif tp == 'D':
            verts.append(dict(type='D', coords=list(cfg.vatoms[v])))
        elif tp == 'W':
            verts.append(dict(type='W', coords=list(cfg.vatoms[v]), ij=list(cfg.Wpar[v])))
        else:
            raise ValueError(tp)
    return verts, step_v


def mg_forms(cfg, lat, maxterms=5):
    """Ground forms a*x_k + b*y_k + (independent atoms of other D vertices, <= 1 per vertex) + (W's):
    list of (e, (a, b), i, j)."""
    import itertools
    D = cfg.indepD
    Ws = sorted(cfg.Wpar)
    out = []
    for k in D:
        others = [v for v in D if v != k]
        for (a, b) in MG_FAMS:
            for assign in itertools.product((0, 1, 2), repeat=len(others)):
                for wsel in itertools.product((0, 1), repeat=len(Ws)):
                    if 2 + sum(1 for t in assign if t) + sum(wsel) > maxterms:
                        continue
                    f = [Fraction(0)] * cfg.N
                    f[cfg.vatoms[k][0]] += a
                    f[cfg.vatoms[k][1]] += b
                    gi = gj = 0
                    for v, t in zip(others, assign):
                        if t == 1:
                            f[cfg.vatoms[v][0]] += 1; gi += 1
                        elif t == 2:
                            f[cfg.vatoms[v][1]] += 1; gj += 1
                    for w, s_ in zip(Ws, wsel):
                        if s_:
                            f[cfg.vatoms[w][0]] += 1
                            gi += cfg.Wpar[w][0]; gj += cfg.Wpar[w][1]
                    e = lat.form_e(f)
                    if e is not None:
                        out.append((e, (a, b), gi, gj))
    return out


def build_merged_tagged(cfg, lat, M, cuts_info, autos, mg=False, rshare=False, rwmap=None, vec=False, sgrid=0,
                        pmerge=False, xshare=False):
    B_ = lat.B
    # merges: copy-step maps + automorphisms; keep explicit edges
    edges = []
    # copy-step maps of independent copies (V = []): tau maps the copied vertex to its copy; as a coordinate
    # permutation this is the corresponding D-vertex swap (only flats inside the copied vertex are merged)
    verts, step_v = cert_vertices(cfg)
    has_c = bool(step_v)
    if has_c:
        assert not autos, "no automorphisms with conditional copies"
    for t, st in enumerate(cfg.steps):
        if st['kind'] == 'copy':
            if st['V']:
                # conditional copy: tau maps the atoms to the new coordinates and fixes the given forms
                src = [cfg.coords(B_, unit(cfg.N, c)) for c in st['atoms']]
                img = [cfg.coords(B_, unit(cfg.N, c)) for c in st['new']]
                fixed = [cfg.coords(B_, f) for f in st['V']]
                # coordinates of later independent (D, W) vertices are fixed too: they are independent of
                # (U, c), so (c, V, later) has the law of (s, V, later)
                later = [cv for t2, st2 in enumerate(cfg.steps) if t2 > t and
                         (st2['kind'] == 'fresh' or (st2['kind'] == 'copy' and not st2['V'])) for cv in st2['new']]
                fixed += [cfg.coords(B_, unit(cfg.N, cv)) for cv in later]
                for (Ff, G, gF, gI) in sub_system_merges_img(lat, merge_gens(lat, src, img, fixed)):
                    edges.append((Ff, G, tuple(gF), ('cmerge', step_v[t], tuple(gI))))
                continue
            perm = {}
            for a, b in zip(st['atoms'], st['new']):
                perm[a] = b
                perm[b] = a
            src = [cfg.coords(B_, unit(cfg.N, c)) for c in st['atoms']]
            img = [cfg.coords(B_, unit(cfg.N, c)) for c in st['new']]
            for (Ff, G, gF) in sub_system_merges(lat, merge_gens(lat, src, img, [])):
                edges.append((Ff, G, tuple(gF), tuple(sorted(perm.items()))))
    for perm in autos:
        src = [cfg.coords(B_, unit(cfg.N, c)) for c in range(cfg.N)]
        img = [cfg.coords(B_, unit(cfg.N, perm.get(c, c))) for c in range(cfg.N)]
        for (Ff, G, gF) in sub_system_merges(lat, merge_gens(lat, src, img, [])):
            edges.append((Ff, G, tuple(gF), tuple(sorted(perm.items()))))
    if pmerge:
        # partial substitutions: a flat whose forms touch only x_k (or only y_k) of a D copy, or a W, has the law of
        # its image with that part moved to an untouched vertex coordinate of the same marginal law
        # with conditional copies only flats avoiding the C coordinates are used (D/W coordinates alone are
        # mutually independent with the product law)
        Dv = [tuple(cfg.vatoms[v]) for v in cfg.indepD]
        Wv = [(cfg.vatoms[w][0], tuple(cfg.Wpar[w])) for w in sorted(cfg.Wpar)]
        dwc = set(c for pr in Dv for c in pr) | set(w for w, ij in Wv)
        npm = 0
        for Ff in range(1, lat.nflats):
            gF = lat.gens_of(Ff)
            sup = set()
            for e in gF:
                sup |= {c for c, x in enumerate(lat.amb[e]) if x != 0}
            if not sup <= dwc:
                continue
            moves = []
            freeD = [(x, y) for (x, y) in Dv if x not in sup and y not in sup]
            freeX = [x for (x, y) in freeD] + [w for (w, ij) in Wv if ij == (1, 0) and w not in sup]
            freeY = [y for (x, y) in freeD] + [w for (w, ij) in Wv if ij == (0, 1) and w not in sup]
            for (x, y) in Dv:
                if x in sup and y not in sup:
                    moves += [(x, t) for t in freeX]
                elif y in sup and x not in sup:
                    moves += [(y, t) for t in freeY]
                elif x in sup and y in sup:
                    moves += [((x, y), t) for t in freeD]
            for (w, ij) in Wv:
                if w in sup:
                    tg = [w2 for (w2, ij2) in Wv if ij2 == ij and w2 not in sup]
                    if ij == (1, 0):
                        tg += [x for (x, y) in freeD]
                    elif ij == (0, 1):
                        tg += [y for (x, y) in freeD]
                    moves += [(w, t) for t in tg]
            if pmerge == 3:
                # all permutations within each group of touched lone parts with the same marginal law
                import itertools as _it
                loneX = [x for (x, y) in Dv if x in sup and y not in sup] + \
                        [w for (w, ij) in Wv if ij == (1, 0) and w in sup]
                loneY = [y for (x, y) in Dv if y in sup and x not in sup] + \
                        [w for (w, ij) in Wv if ij == (0, 1) and w in sup]
                for grp in (loneX, loneY):
                    for pg in _it.permutations(grp):
                        if list(pg) != grp:
                            moves.append(('perm', tuple(zip(grp, pg))))
            if pmerge == 2:
                # exchanges of two touched lone parts with the same marginal law (x_k alone, y_k alone, W's)
                loneX = [x for (x, y) in Dv if x in sup and y not in sup] + \
                        [w for (w, ij) in Wv if ij == (1, 0) and w in sup]
                loneY = [y for (x, y) in Dv if y in sup and x not in sup] + \
                        [w for (w, ij) in Wv if ij == (0, 1) and w in sup]
                for grp in (loneX, loneY):
                    for i1 in range(len(grp)):
                        for i2 in range(i1 + 1, len(grp)):
                            moves.append((grp[i1], grp[i2]))
                for ij0 in set(ij for (w, ij) in Wv if ij not in ((1, 0), (0, 1))):
                    grp = [w for (w, ij) in Wv if ij == ij0 and w in sup]
                    for i1 in range(len(grp)):
                        for i2 in range(i1 + 1, len(grp)):
                            moves.append((grp[i1], grp[i2]))
            for src_, tgt in moves:
                pm_ = {}
                if src_ == 'perm':
                    pm_ = {a: b for a, b in tgt if a != b}
                elif isinstance(src_, tuple):
                    (a1, b1), (a2, b2) = src_, tgt
                    pm_ = {a1: a2, a2: a1, b1: b2, b2: b1}
                else:
                    pm_ = {src_: tgt, tgt: src_}
                img = []
                for e in gF:
                    a = lat.amb[e]
                    g = list(a)
                    for c1, c2 in pm_.items():
                        g[c2] = a[c1]
                    e2 = lat.form_e(g)
                    if e2 is None:
                        img = None
                        break
                    img.append(e2)
                if img is None:
                    continue
                G2 = lat.cl_ids(img)
                if G2 != Ff:
                    edges.append((Ff, G2, tuple(gF), ('pmerge', tuple(sorted(pm_.items())))))
                    npm += 1
        print(f"  pmerge edges {npm}", flush=True)
    uf = UF(lat.nflats)
    for (Ff, G, gF, pm) in edges:
        uf.union(Ff, G)
    cls = np.array([uf.find(i) for i in range(lat.nflats)], dtype=np.int64)
    zc = cls[0]
    uniq = [int(c) for c in np.unique(cls) if c != zc]
    pos = {c: i for i, c in enumerate(uniq)}
    colof = np.array([pos.get(int(c), -1) for c in cls], dtype=np.int64)
    nfc = len(uniq)
    gcol = {}
    for i in range(M + 1):
        for j in range(M + 1):
            gcol[(i, j)] = 2 * nfc + len(gcol)
    mcol = {}
    if mg:
        for cp in (0, 1):
            for fam in MG_FAMS:
                for i in range(M + 1):
                    for j in range(M + 1):
                        mcol[(cp, fam, i, j)] = 2 * nfc + len(gcol) + len(mcol)
    scol = {}
    if sgrid:
        # signed grid g(a, a', b, b') = H(sum of a mu-, a' (-mu)-, b nu-, b' (-nu)-summands, independent), keyed up
        # to negation symmetry; total number of summands <= sgrid
        def sk(t):
            return min(tuple(t), (t[1], t[0], t[3], t[2]))
        for tot in range(sgrid + 1):
            for a in range(tot + 1):
                for a2 in range(tot + 1 - a):
                    for b in range(tot + 1 - a - a2):
                        k_ = sk((a, a2, b, tot - a - a2 - b))
                        if k_ not in scol:
                            scol[k_] = 2 * nfc + len(gcol) + len(mcol) + len(scol)
    Lc = 2 * nfc + len(gcol) + len(mcol) + len(scol)
    ncol = Lc + 1
    rows, tags, lo, hi = [], [], [], []
    seen = {}
    INF = np.inf

    phi_flat = None
    if rshare == 'full':
        # full reflection sharing: copy 1 is identified with phi(copy 0) flat by flat, so copy 1's flats use the
        # columns of their phi-images in copy 0 (requires a phi-closed ground set and a W map covering all W's)
        Dc_ = [cfg.vatoms[v] for v, tp in enumerate(cfg.vtype) if tp == 'D']
        wm_ = {int(a): int(b) for a, b in (rwmap or [])}
        assert set(wm_) == set(cfg.vatoms[w][0] for w in cfg.Wpar) == set(wm_.values()), "full rshare: W map"
        assert all(t in ('D', 'W') for t in cfg.vtype), "full rshare: D and W vertices only"

        def phi_form(a):
            g = [0 * x for x in a]
            for (x, y) in Dc_:
                g[x], g[y] = -a[y], -a[x]
            for wa, wb in wm_.items():
                g[wb] -= a[wa]
            return g
        phi_e = [lat.form_e(phi_form(lat.amb[e])) for e in range(len(lat.amb))]
        assert all(e2 is not None for e2 in phi_e), "full rshare: ground set not phi-closed"
        phi_flat = np.zeros(lat.nflats, dtype=np.int64)
        for f in range(1, lat.nflats):
            phi_flat[f] = lat.cl_ids([phi_e[e] for e in lat.gens_of(f)])
        assert all(phi_flat[phi_flat[f]] == f for f in range(lat.nflats)), "phi is not an involution on flats"

    def col(cp, f):
        if cp == 1 and phi_flat is not None:
            f = phi_flat[f]
        c = colof[f]
        return None if c < 0 else int(c) + (cp * nfc if phi_flat is None else 0)

    def add(terms, l, h, tag, dedup=True):
        d = {}
        for c, a in terms:
            if c is None:
                continue
            d[c] = d.get(c, 0) + a
        d = {c: a for c, a in d.items() if a != 0}
        if not d:
            return
        key = (tuple(sorted(d.items())), l, h)
        if dedup and key in seen:
            return
        seen[key] = len(rows)
        rows.append(d); lo.append(l); hi.append(h); tags.append(tag)
    MA, MK, A, Bv, J, K = shannon_arrays(lat)
    shblock = None
    shcmaps = None
    if vec:
        # vectorized Shannon rows (deduplicated by their merged-column signature), stored before all other rows
        cmaps = []
        for cp in (0, 1):
            f = np.arange(lat.nflats) if (cp == 0 or phi_flat is None) else phi_flat
            cm = colof[f].astype(np.int64)
            cm = np.where(cm >= 0, cm + (cp * nfc if phi_flat is None else 0), -1)
            cmaps.append(cm)
        keepm = colof[MA] != colof[MK]
        ma, mk = MA[keepm], MK[keepm]
        Cs, Vs, kinds, cps, aa, bb, jj, kk = [], [], [], [], [], [], [], []
        for cp in (0, 1):
            cm = cmaps[cp]
            n1 = len(ma)
            Cs.append(np.stack([cm[ma], cm[mk], np.full(n1, -1), np.full(n1, -1)], 1))
            Vs.append(np.tile(np.array([1, -1, 0, 0], dtype=np.int64), (n1, 1)))
            kinds.append(np.zeros(n1, np.int8)); cps.append(np.full(n1, cp, np.int8))
            aa.append(ma); bb.append(np.zeros(n1, np.int64)); jj.append(np.zeros(n1, np.int64)); kk.append(mk)
            n2 = len(A)
            Cs.append(np.stack([cm[A], cm[Bv], cm[J], cm[K]], 1))
            Vs.append(np.tile(np.array([1, 1, -1, -1], dtype=np.int64), (n2, 1)))
            kinds.append(np.ones(n2, np.int8)); cps.append(np.full(n2, cp, np.int8))
            aa.append(A); bb.append(Bv); jj.append(J); kk.append(K)
        C_, V_ = canon_rows(np.concatenate(Cs), np.concatenate(Vs))
        del Cs, Vs
        nz = (V_ != 0).any(axis=1)
        idx0 = np.nonzero(nz)[0]
        sig = np.concatenate([C_[idx0], V_[idx0]], axis=1)
        _, first = np.unique(sig, axis=0, return_index=True)
        del sig
        sel = idx0[np.sort(first)]
        C_, V_ = C_[sel], V_[sel]
        kind_ = np.concatenate(kinds)[sel]; cp_ = np.concatenate(cps)[sel]
        a_ = np.concatenate(aa)[sel]; b_ = np.concatenate(bb)[sel]; j_ = np.concatenate(jj)[sel]
        k_ = np.concatenate(kk)[sel]
        shblock = (C_, V_, kind_, cp_, a_, b_, j_, k_)
        shcmaps = cmaps
    else:
        for cp in (0, 1):
            for a, k in zip(MA, MK):
                if colof[a] != colof[k]:
                    add([(col(cp, a), 1), (col(cp, k), -1)], 0, INF, ('mono', cp, int(a), int(k)))
            for a, b, j, k in zip(A, Bv, J, K):
                add([(col(cp, a), 1), (col(cp, b), 1), (col(cp, j), -1), (col(cp, k), -1)], 0, INF,
                    ('sub', cp, int(a), int(b), int(j), int(k)))
    cis, ccis = [], []
    for t, st in enumerate(cfg.steps):
        if st['kind'] == 'fresh' or (st['kind'] == 'copy' and not st['V']):
            new = sorted(st['new'])
            old = list(range(min(new)))
            if not old:
                continue
            Fo = lat.cl_ids([lat.coord_e[c] for c in old])
            Fn = lat.cl_ids([lat.coord_e[c] for c in new])
            Fa = lat.cl_ids([lat.coord_e[c] for c in old + new])
            cis.append((old, new, Fo, Fn, Fa))
        elif st['kind'] == 'copy':
            new = sorted(st['new'])
            old = list(range(min(new)))
            Ve = [lat.form_e(f) for f in st['V']]
            assert all(e is not None for e in Ve), "given forms must be ground"
            ne = [lat.coord_e[c] for c in new]
            oe = [lat.coord_e[c] for c in old]
            ccis.append((step_v[t], lat.cl_ids(Ve + ne), lat.cl_ids(oe), lat.cl_ids(oe + ne), lat.cl_ids(Ve)))
        else:
            raise ValueError("cert4: unsupported step")
    for cp in (0, 1):
        for (old, new, Fo, Fn, Fa) in cis:
            add([(col(cp, Fn), 1), (col(cp, Fo), 1), (col(cp, Fa), -1)], 0, 0, ('ci', cp, tuple(old), tuple(new), Fn, Fo, Fa),
                dedup=False)
        # conditional independence of a conditional copy: H(V+new) + H(old) - H(old+new) - H(V) = 0
        for (vk, Fa_, Fo_, Fj_, Fk_) in ccis:
            add([(col(cp, Fa_), 1), (col(cp, Fo_), 1), (col(cp, Fj_), -1), (col(cp, Fk_), -1)], 0, 0,
                ('cci', cp, vk, Fa_, Fo_, Fj_, Fk_), dedup=False)
    Dv = [v for v, t in enumerate(cfg.vtype) if t == 'D']
    dflats = [lat.cl_ids([lat.coord_e[cfg.vatoms[v][0]], lat.coord_e[cfg.vatoms[v][1]]]) for v in Dv]
    for cp in (0, 1):
        for e, labs in enumerate(lat.labels):
            fl = int(lat.nxt[0, e])
            if 'sumXY' in labs:
                add([(col(cp, fl), 1)], -INF, 1.0, ('bsum', cp, e, fl))
            if 'diffXY' in labs:
                add([(col(cp, fl), 1), (Lc, -1)], -INF, 0.0, ('bdiff', cp, e, fl))
            if 'atomX' in labs or 'atomY' in labs:
                add([(col(cp, fl), 1)], -INF, 1.0, ('batom', cp, e, fl))
        for k, Fk in enumerate(dflats):
            add([(col(cp, Fk), 1), (Lc, -1)], 0, 0, ('dpair', cp, k, Fk), dedup=False)
    G = lambda i, j: gcol.get((i, j))
    add([(G(0, 0), 1)], 0, 0, ('g_h00',))
    for (i, j), c in gcol.items():
        add([(c, 1)], 0, INF, ('g_nonneg', i, j))
        if G(i + 1, j) is not None:
            add([(G(i + 1, j), 1), (c, -1)], 0, INF, ('g_monox', i, j))
        if G(i, j + 1) is not None:
            add([(G(i, j + 1), 1), (c, -1)], 0, INF, ('g_monoy', i, j))
        if G(i + 2, j) is not None:
            add([(G(i + 1, j), 2), (c, -1), (G(i + 2, j), -1)], 0, INF, ('g_concx', i, j))
        if G(i, j + 2) is not None:
            add([(G(i, j + 1), 2), (c, -1), (G(i, j + 2), -1)], 0, INF, ('g_concy', i, j))
        if G(i + 1, j) is not None and G(i, j + 1) is not None:
            add([(G(i + 1, j), 1), (G(i, j + 1), 1), (c, -1), (Lc, -1)], 0, INF, ('g_link', i, j))
    add([(G(1, 1), 1)], -INF, 1.0, ('g_h11',))
    for cp in (0, 1):
        for (e, i, j) in grid_forms(cfg, lat):
            gi, gj = (i, j) if cp == 0 else (j, i)
            if (gi, gj) in gcol:
                fl = int(lat.nxt[0, e])
                add([(col(cp, fl), 1), (gcol[(gi, gj)], -1)], 0, 0, ('ident', cp, e, i, j, fl), dedup=False)
    if sgrid:
        S_ = lambda t: scol.get(sk(t))
        dirs = [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]
        plus = lambda t, d, m=1: tuple(x + m * y for x, y in zip(t, d))
        for (a, b), gc_ in gcol.items():
            c_ = S_((a, 0, b, 0))
            if c_ is not None:
                add([(c_, 1), (gc_, -1)], 0, 0, ('sg_h', (a, b)))
        for k_, c_ in scol.items():
            add([(c_, 1)], 0, INF, ('sg_nonneg', k_))
            for d in dirs:
                c1, c2 = S_(plus(k_, d)), S_(plus(k_, d, 2))
                if c1 is not None:
                    add([(c1, 1), (c_, -1)], 0, INF, ('sg_mono', k_, d))
                if c2 is not None:
                    add([(c1, 2), (c_, -1), (c2, -1)], 0, INF, ('sg_conc', k_, d))
            for dx, dy in (((1, 0, 0, 0), (0, 0, 1, 0)), ((0, 1, 0, 0), (0, 0, 0, 1))):
                c1, c2 = S_(plus(k_, dx)), S_(plus(k_, dy))
                if c1 is not None and c2 is not None:
                    add([(c1, 1), (c2, 1), (c_, -1), (Lc, -1)], 0, INF, ('sg_link', k_, dx))
        add([(S_((1, 0, 0, 1)), 1), (Lc, -1)], -INF, 0.0, ('sg_diff',))
        Dvs = [cfg.vatoms[v] for v in cfg.indepD]
        Ws = [(cfg.vatoms[w][0], cfg.Wpar[w]) for w in sorted(cfg.Wpar)]
        for e in range(len(lat.amb)):
            f = [Fraction(x) for x in lat.amb[e]]
            if any(x not in (-1, 0, 1) for x in f):
                continue
            nat = [0, 0, 0, 0]     # (+x, -x, +y, -y) counts with W's contributing their (i, j)
            ok = True
            used = set()
            for (x, y) in Dvs:
                if f[x] != 0 and f[y] != 0:
                    ok = False
                if f[x] == 1: nat[0] += 1
                if f[x] == -1: nat[1] += 1
                if f[y] == 1: nat[2] += 1
                if f[y] == -1: nat[3] += 1
                used |= {x, y}
            for (wc, (wi, wj)) in Ws:
                used.add(wc)
                if f[wc] == 1:
                    nat[0] += wi; nat[2] += wj
                elif f[wc] == -1:
                    nat[1] += wi; nat[3] += wj
            if not ok or any(f[c] != 0 for c in range(len(f)) if c not in used) or sum(nat) == 0:
                continue
            fl = int(lat.nxt[0, e])
            for cp in (0, 1):
                t = tuple(nat) if cp == 0 else (nat[3], nat[2], nat[1], nat[0])
                c_ = S_(t)
                if c_ is not None:
                    add([(col(cp, fl), 1), (c_, -1)], 0, 0, ('sg_ident', cp, e, t, fl), dedup=False)
    if mg:
        for cp in (0, 1):
            Hc = (lambda i, j: gcol.get((i, j))) if cp == 0 else (lambda i, j: gcol.get((j, i)))
            for fam in MG_FAMS:
                g = lambda i, j, fam=fam, cp=cp: mcol.get((cp, fam, i, j))
                for i in range(M + 1):
                    for j in range(M + 1):
                        c = g(i, j)
                        add([(c, 1)], 0, INF, ('mg_nonneg', cp, fam, i, j))
                        if g(i + 1, j) is not None:
                            add([(g(i + 1, j), 1), (c, -1)], 0, INF, ('mg_monox', cp, fam, i, j))
                        if g(i, j + 1) is not None:
                            add([(g(i, j + 1), 1), (c, -1)], 0, INF, ('mg_monoy', cp, fam, i, j))
                        if g(i + 2, j) is not None:
                            add([(g(i + 1, j), 2), (c, -1), (g(i + 2, j), -1)], 0, INF, ('mg_concx', cp, fam, i, j))
                        if g(i, j + 2) is not None:
                            add([(g(i, j + 1), 2), (c, -1), (g(i, j + 2), -1)], 0, INF, ('mg_concy', cp, fam, i, j))
                        add([(c, 1), (Hc(i, j), -1)], 0, INF, ('mg_geh', cp, fam, i, j))
                        if Hc(i + 1, j) is not None:
                            add([(Hc(i + 1, j), 1), (Hc(0, 1), 1), (c, -1)], 0, INF, ('mg_le1', cp, fam, i, j))
                            add([(c, 1), (Hc(0, 1), 1), (Hc(i + 1, j), -1)], 0, INF, ('mg_ge1', cp, fam, i, j))
                        if fam == (1, 1) and Hc(i, j + 1) is not None:
                            add([(Hc(i, j + 1), 1), (Hc(1, 0), 1), (c, -1)], 0, INF, ('mg_le2', cp, fam, i, j))
                            add([(c, 1), (Hc(1, 0), 1), (Hc(i, j + 1), -1)], 0, INF, ('mg_ge2', cp, fam, i, j))
            for (e, fam, i, j) in mg_forms(cfg, lat):
                if (cp, fam, i, j) in mcol:
                    fl = int(lat.nxt[0, e])
                    add([(col(cp, fl), 1), (mcol[(cp, fam, i, j)], -1)], 0, 0, ('mgident', cp, fam, e, i, j, fl),
                        dedup=False)
    if xshare:
        # cross-copy partial identification: a copy-1 flat has the law of the copy-0 flat obtained by mapping each
        # touched part of a copy-1 vertex to the negation of a copy-0 part with the same law: pair (x', y') ->
        # (-y_m, -x_m); lone x' or W'(1,0) (law mu' = law(-Y1)) -> -(lone y_m) or -(W(0,1)); lone y' or W'(0,1)
        # (law nu' = law(-X1)) -> -(lone x_m) or -(W(1,0)); W'(i,j) -> -W(j,i); distinct vertices to distinct vertices
        import itertools as _it
        assert phi_flat is None
        Dv = [tuple(cfg.vatoms[v]) for v in cfg.indepD]
        Wv = [(cfg.vatoms[w][0], tuple(cfg.Wpar[w])) for w in sorted(cfg.Wpar)]
        dwc_ = set(c for pr in Dv for c in pr) | set(w for w, ij in Wv)
        nxs = 0
        seenx = set()
        for f1 in range(1, lat.nflats):
            gF = lat.gens_of(f1)
            sup = set()
            for e in gF:
                sup |= {c for c, x in enumerate(lat.amb[e]) if x != 0}
            if not sup <= dwc_:
                continue                     # flats touching C coordinates are not shared
            # parts of copy 1: ('P', k) pair, ('X', c) mu'-type lone coordinate, ('Y', c) nu'-type, ('W', c, ij)
            parts = []
            for k, (x, y) in enumerate(Dv):
                if x in sup and y in sup:
                    parts.append(('P', k))
                elif x in sup:
                    parts.append(('X', x))
                elif y in sup:
                    parts.append(('Y', y))
            for (w, ij) in Wv:
                if w in sup:
                    parts.append(('X', w) if ij == (1, 0) else ('Y', w) if ij == (0, 1) else ('W', w, ij))
            # copy-0 target slots: ('D', m) whole vertex, or single coordinates
            def opts(pt):
                if pt[0] == 'P':
                    return [('D', m) for m in range(len(Dv))]
                if pt[0] == 'X':     # law of -Y1: lone y_m (vertex m) or a W(0,1)
                    return [('y', m) for m in range(len(Dv))] + [('w', w) for (w, ij) in Wv if ij == (0, 1)]
                if pt[0] == 'Y':
                    return [('x', m) for m in range(len(Dv))] + [('w', w) for (w, ij) in Wv if ij == (1, 0)]
                return [('w', w) for (w, ij) in Wv if ij == (pt[2][1], pt[2][0])]
            if len(parts) > 6:
                continue
            for choice in _it.product(*[opts(pt) for pt in parts]):
                verts_used = [('D', c[1]) if c[0] in ('D', 'x', 'y') else ('W', c[1]) for c in choice]
                if len(set(verts_used)) != len(verts_used):
                    continue
                cmap = {}
                for pt, c in zip(parts, choice):
                    if pt[0] == 'P':
                        x, y = Dv[pt[1]]; xm, ym = Dv[c[1]]
                        cmap[x] = ym; cmap[y] = xm
                    else:
                        src = pt[1]
                        tgt = Dv[c[1]][1] if c[0] == 'y' else Dv[c[1]][0] if c[0] == 'x' else c[1]
                        cmap[src] = tgt
                img = []
                for e in gF:
                    a = lat.amb[e]
                    g = [0 * t for t in a]
                    for c1, c2 in cmap.items():
                        g[c2] -= a[c1]
                    e2 = lat.form_e(g)
                    if e2 is None:
                        img = None
                        break
                    img.append(e2)
                if img is None:
                    continue
                f0 = lat.cl_ids(img)
                key = (f1, f0)
                if key in seenx:
                    continue
                seenx.add(key)
                add([(col(1, f1), 1), (col(0, f0), -1)], 0, 0, ('xshare', f1, f0, tuple(sorted(cmap.items()))))
                nxs += 1
        print(f"  xshare rows {nxs}", flush=True)
    if rshare:
        # copy 1's D vertices are realised as phi(D_k) = (-Y_k, -X_k) of copy 0's D vertices: identify D-only flats
        # with rwmap {a: b}, copy 1's W vertex a (law mu'^i nu'^j) is realised as -W_b of copy 0 (law mu^j nu^i)
        Dc = [cfg.vatoms[v] for v, tp in enumerate(cfg.vtype) if tp == 'D']
        dset = set(cc for pr in Dc for cc in pr)
        wm = {int(a): int(b) for a, b in (rwmap or [])}
        assert len(set(wm.values())) == len(wm)
        for a, b in wm.items():
            ia, ja = cfg.Wpar[cfg.atom_v[a]]
            assert cfg.Wpar[cfg.atom_v[b]] == (ja, ia), (a, b)
        allowed = dset | set(wm)
        for f in range(1, lat.nflats):
            gens = lat.gens_of(f)
            forms = [lat.amb[e] for e in gens]
            if any(any(x != 0 for k, x in enumerate(a) if k not in allowed) for a in forms):
                continue
            img = []
            for a in forms:
                g = [0 * x for x in a]
                for (x, y) in Dc:
                    g[x], g[y] = -a[y], -a[x]
                for wa, wb in wm.items():
                    g[wb] -= a[wa]
                e2 = lat.form_e(g)
                if e2 is None:
                    img = None
                    break
                img.append(e2)
            if img is None:
                continue
            f0 = lat.cl_ids(img)
            add([(col(1, f), 1), (col(0, f0), -1)], 0, 0, ('rshare', f, f0), dedup=True)
    cache = {}

    def Jn(*fs):
        key = tuple(sorted(set(fs)))
        if key not in cache:
            es = []
            for f in key:
                es += lat.gens_of(f)
            cache[key] = lat.cl_ids(es)
        return cache[key]
    cutrows = []
    for info in cuts_info:
        if info[0] == 'M4':
            s, a, b, c_, d = info[1:]
            row = matus_row(s, a, b, c_, d, Jn)
        else:
            fam, k, variant, a, b, c_, d, z = info
            row = five_row(fam, k, a, b, c_, d, z, variant, Jn)
        for cp in (0, 1):
            add([(col(cp, f), w) for f, w in row.items()], 0, INF, ('cut', cp, info, tuple(sorted(row.items()))))
    ri, rj, rv = [], [], []
    for r, d in enumerate(rows):
        for c, a in d.items():
            ri.append(r); rj.append(c); rv.append(a)
    Amat = sp.csr_matrix((rv, (ri, rj)), shape=(len(rows), ncol))
    lo, hi = np.array(lo), np.array(hi)
    shash = None
    if shblock is not None:
        C_, V_, kind_, cp_, a_, b_, j_, k_ = shblock
        n_sh = len(kind_)
        m = C_ >= 0
        rr = np.repeat(np.arange(n_sh), m.sum(axis=1))
        S_ = sp.csr_matrix((V_[m].astype(float), (rr, C_[m])), shape=(n_sh, ncol))
        Amat = sp.vstack([S_, Amat]).tocsr()
        lo = np.concatenate([np.zeros(n_sh), lo]); hi = np.concatenate([np.full(n_sh, INF), hi])
        tags = LazyTags(kind_, cp_, a_, b_, j_, k_, tags)
        shash = row_hash(C_, V_)
    return dict(A=Amat, lo=lo, hi=hi, ncol=ncol, obj_col=Lc, tags=tags, colof=colof, nfc=nfc,
                gcol=gcol, edges=edges, cls=cls, Lc=Lc, rwmap=sorted([int(a), int(b)] for a, b in (rwmap or [])),
                phi_flat=phi_flat, shash=shash, cmaps=shcmaps)


def exact_dual(L, y, tol=1e-9):
    A = L['A'].tocsr()
    supp = np.nonzero(np.abs(y) > tol)[0]
    sub = A[supp]
    cols = np.unique(np.concatenate([sub.indices, [L['obj_col']]]))
    cpos = {c: i for i, c in enumerate(cols)}
    nr, nc = len(cols), len(supp)
    Mrows = [[0] * (nc + 1) for _ in range(nr)]
    subc = sub.tocoo()
    for j, c, v in zip(subc.row, subc.col, subc.data):
        Mrows[cpos[c]][j] = int(round(v))
    Mrows[cpos[L['obj_col']]][nc] = 1
    Mq = flint.fmpq_mat(Mrows)
    R, rank = Mq.rref()
    piv = []
    r = 0
    for c in range(nc + 1):
        if r < rank and R[r, c] != 0:
            piv.append(c)
            r += 1
    if nc in piv:
        raise RuntimeError("objective not in span of support rows")
    pset = set(piv)
    free = [c for c in range(nc) if c not in pset]
    yfree = {c: Fraction(float(y[supp[c]])).limit_denominator(10 ** 6) for c in free}
    yex = {int(supp[c]): v for c, v in yfree.items() if v != 0}
    for k, c in enumerate(piv):
        q = R[k, nc]
        val = Fraction(int(q.p), int(q.q))
        for f in free:
            rkf = R[k, f]
            if rkf != 0 and yfree[f] != 0:
                val -= Fraction(int(rkf.p), int(rkf.q)) * yfree[f]
        if val != 0:
            yex[int(supp[c])] = val
    return yex


def explicit_certificate(cfg, lat, L, yex, M, autos):
    """Explicit rows (flat level) + tree-flow merge rows; returns (rows json, lambda)."""
    def form(e):
        return [str(x) for x in lat.amb[e]]

    def gens(f):
        return [form(e) for e in lat.gens_of(f)]
    swap = autos[0] if autos else None
    out = []
    lam = Fraction(0)
    imb = {}          # (cp, flat) -> coefficient in the explicit sum

    def acc(cp, f, c):
        if f != 0 and c != 0:
            imb[(cp, f)] = imb.get((cp, f), 0) + c
    for r, v in sorted(yex.items()):
        t = L['tags'][r]
        lo, hi = L['lo'][r], L['hi'][r]
        ineq_ge = np.isinf(hi) and not np.isinf(lo)
        mult = -v if ineq_ge else v
        if np.isinf(lo) and not np.isinf(hi):
            lam += v * Fraction(hi)
        kind = t[0]
        # explicit flat-level contribution of y_r * a_r (a_r = LP row with these representatives)
        if kind == 'mono':
            _, cp, a, k = t
            acc(cp, a, v); acc(cp, k, -v)
            e = int(np.nonzero(lat.nxt[k] == a)[0][0])
            out.append(dict(type='mono', copy=cp, K=gens(k), i=form(e), mult=str(mult)))
        elif kind == 'sub':
            _, cp, a, b, j, k = t
            acc(cp, a, v); acc(cp, b, v); acc(cp, j, -v); acc(cp, k, -v)
            e1 = int(np.nonzero(lat.nxt[k] == a)[0][0])
            e2 = int(np.nonzero(lat.nxt[k] == b)[0][0])
            out.append(dict(type='sub', copy=cp, K=gens(k), i=form(e1), j=form(e2), mult=str(mult)))
        elif kind == 'ci':
            _, cp, old, new, Fn, Fo, Fa = t
            acc(cp, Fn, v); acc(cp, Fo, v); acc(cp, Fa, -v)
            out.append(dict(type='ci', copy=cp, old=list(old), new=list(new), mult=str(mult)))
        elif kind == 'cci':
            _, cp, vk, Fa_, Fo_, Fj_, Fk_ = t
            acc(cp, Fa_, v); acc(cp, Fo_, v); acc(cp, Fj_, -v); acc(cp, Fk_, -v)
            out.append(dict(type='cci', copy=cp, vertex=vk, mult=str(mult)))
        elif kind in ('bsum', 'batom'):
            _, cp, e, fl = t
            acc(cp, fl, v)
            out.append(dict(type=kind, copy=cp, f=form(e), mult=str(mult)))
        elif kind == 'bdiff':
            _, cp, e, fl = t
            acc(cp, fl, v)
            out.append(dict(type=kind, copy=cp, f=form(e), mult=str(mult)))
        elif kind == 'dpair':
            _, cp, k, Fk = t
            acc(cp, Fk, v)
            out.append(dict(type='dpair', copy=cp, vertex=k, mult=str(mult)))
        elif kind.startswith('g_'):
            out.append(dict(type=kind, ij=list(t[1:]), mult=str(mult)))
        elif kind == 'ident':
            _, cp, e, i, j, fl = t
            acc(cp, fl, v)
            fe = form(e)
            if all(Fraction(x) <= 0 for x in fe):     # grid forms are written with coefficients +1 (H(-f) = H(f))
                fe = [str(-Fraction(x)) for x in fe]
            out.append(dict(type='ident', copy=cp, f=fe, ij=[i, j], mult=str(mult)))
        elif kind == 'xshare':
            _, f1, f0, cm = t
            acc(1, f1, v); acc(0, f0, -v)
            out.append(dict(type='xshare', G=gens(f1), map=[[a, b] for a, b in cm], mult=str(mult)))
        elif kind == 'rshare':
            _, f1, f0 = t
            acc(1, f1, v); acc(0, f0, -v)
            rr = dict(type='rshare', G=gens(f1), mult=str(mult))
            if L.get('rwmap'):
                rr['wmap'] = L['rwmap']
            out.append(rr)
        elif kind == 'sg_ident':
            _, cp, e, tt, fl = t
            acc(cp, fl, v)
            out.append(dict(type='sg_ident', copy=cp, f=form(e), t=list(tt), mult=str(mult)))
        elif kind in ('sg_nonneg', 'sg_h', 'sg_mono', 'sg_conc', 'sg_link', 'sg_diff'):
            rr = dict(type=kind, mult=str(mult))
            if kind == 'sg_h':
                rr['ab'] = list(t[1])
            elif kind != 'sg_diff':
                rr['t'] = list(t[1])
                if kind in ('sg_mono', 'sg_conc'):
                    rr['d'] = list(t[2])
                if kind == 'sg_link':
                    rr['dx'] = list(t[2])
            out.append(rr)
        elif kind.startswith('mg_'):
            _, cp, fam, i, j = t
            out.append(dict(type=kind, copy=cp, fam=list(fam), ij=[i, j], mult=str(mult)))
        elif kind == 'mgident':
            _, cp, fam, e, i, j, fl = t
            acc(cp, fl, v)
            out.append(dict(type='mgident', copy=cp, fam=list(fam), f=form(e), ij=[i, j], mult=str(mult)))
        elif kind == 'cut':
            _, cp, info, rowitems = t
            for f, w in rowitems:
                acc(cp, f, v * w)
            if info[0] == 'M4':
                s, a, b, c_, d = info[1:]
                out.append(dict(type='matus4', copy=cp, s=s, vars=[gens(a), gens(b), gens(c_), gens(d)], mult=str(mult)))
            else:
                fam, k, variant, a, b, c_, d, z = info
                out.append(dict(type='five', copy=cp, fam=fam, k=k, variant=variant,
                                vars=[gens(a), gens(b), gens(c_), gens(d), gens(z)], mult=str(mult)))
        else:
            raise ValueError(kind)
    if L.get('phi_flat') is not None:
        # full reflection sharing: move every copy-1 imbalance to copy 0 with an rshare row
        # (LP row a = H_1(f) - H_0(phi f), multiplier v = -imbalance)
        for (cp, f), val in sorted(imb.items()):
            if cp != 1 or val == 0:
                continue
            f0 = int(L['phi_flat'][f])
            v = -val
            acc(1, f, v); acc(0, f0, -v)
            rr = dict(type='rshare', G=gens(f), mult=str(v))
            if L.get('rwmap'):
                rr['wmap'] = L['rwmap']
            out.append(rr)
    # tree flows inside merge classes: imbalance per (cp, flat) must be cancelled by merge rows H(tauF) - H(F)
    adj = {}
    for (Ff, G, gF, pm) in L['edges']:
        adj.setdefault(Ff, []).append((G, Ff, G, gF, pm))     # edge oriented F -> G (G = cl tau gF)
        adj.setdefault(G, []).append((Ff, Ff, G, gF, pm))
    nmerge = 0
    for cp in (0, 1):
        flats = [f for (c, f), val in imb.items() if c == cp and val != 0]
        done = set()
        for f0 in flats:
            if f0 in done or imb.get((cp, f0), 0) == 0:
                continue
            # BFS over the class of f0
            order, parent = [f0], {f0: None}
            q = 0
            while q < len(order):
                u = order[q]; q += 1
                for (w, Ff, G, gF, pm) in adj.get(u, []):
                    if w not in parent:
                        parent[w] = (u, Ff, G, gF, pm)
                        order.append(w)
            done |= set(order)
            for u in reversed(order[1:]):
                val = imb.get((cp, u), 0)
                if val == 0:
                    continue
                p, Ff, G, gF, pm = parent[u]
                # merge row R = H(G) - H(F) (as in check3), multiplier m adds -m*R*(-1)?  We need the total
                # sum_rows mult*R == lambda S - L; the explicit LP rows enter as y*a, i.e. the identity is
                # sum y_r a_r = e_L, and R_r = rhs - a_r.  For merge rows (equalities) R = H(G) - H(F) = -(H(F)-H(G)),
                # LP-form a = H(F) - H(G), contribution y*a.  Cancel imbalance val at u.
                if u == Ff:      # a = H(u) - H(p): choose y = -val
                    y = -val
                    imb[(cp, u)] = 0
                    imb[(cp, p)] = imb.get((cp, p), 0) - y * (-1) if False else imb.get((cp, p), 0) + val
                else:            # u == G: a = H(p) - H(u): choose y = val
                    y = val
                    imb[(cp, u)] = 0
                    imb[(cp, p)] = imb.get((cp, p), 0) + val
                if pm and pm[0] == 'pmerge':
                    out.append(dict(type='pmerge', copy=cp, G=[form(e) for e in gF],
                                    perm=[[a, b] for a, b in pm[1]], mult=str(y)))
                elif pm and pm[0] == 'cmerge':
                    # written on the copy side: R' = H(cl psi G') - H(cl G'), G' = tau gF, so R' = -R
                    out.append(dict(type='cmerge', copy=cp, vertex=pm[1], G=[form(e) for e in pm[2]],
                                    mult=str(-y)))
                else:
                    out.append(dict(type='merge', copy=cp, G=[form(e) for e in gF],
                                    perm=[[a, b] for a, b in pm], mult=str(y)))
                nmerge += 1
            root = order[0]
            if imb.get((cp, root), 0) != 0:
                raise RuntimeError(f"class imbalance does not vanish: {imb[(cp, root)]}")
    verts, _ = cert_vertices(cfg)
    J = dict(problem="two-set exponent: log|X-Y| <= lambda log|X+Y| for finite X, Y in Z",
             config=dict(coords=cfg.N, vertices=verts, note="mutually independent vertices in this order; D = copy of "
                         "(X1,Y1) ~ Gamma, W = variable with law mu^{*i}*nu^{*j}; copy 0 = Gamma, copy 1 = reflected pair "
                         "(-Y,-X) with Gamma' (grid transposed)"),
             grid_depth=M, rows=out, claimed_lambda=f"{lam.numerator}/{lam.denominator}")
    if any(r['type'].startswith('mg') for r in out):
        J['multigrid'] = "g_f(i,j) = H(a x + b y + V_ij), (a,b) in {(1,1),(1,-1)}, per copy"
    if any(v['type'] == 'C' for v in verts):
        J['config']['note'] = ("vertices in this order; D = copy of (X1,Y1) ~ Gamma and W = variable with law "
                               "mu^{*i}*nu^{*j}, each independent of all earlier vertices; C = conditional copy of the "
                               "src coordinates given the given forms (same joint law with the given forms, "
                               "conditionally independent of all earlier coordinates given them); copy 0 = Gamma, "
                               "copy 1 = reflected pair (-Y,-X) with Gamma' (grid transposed)")
    return J, lam, nmerge


def certify(cfg, lat, M, infos, autos, outfile, opts=IPMX, verbose=True, mg=False, rshare=False, rwmap=None):
    t0 = time.time()
    L = build_merged_tagged(cfg, lat, M, infos, autos, mg=mg, rshare=rshare, rwmap=rwmap)
    if verbose:
        print(f"merged tagged LP: {L['A'].shape}, edges {len(L['edges'])}, {time.time()-t0:.1f}s", flush=True)
    S = solve_lp(L, opts=opts)
    if verbose:
        print(f"value {S['value']:.12f} {S['status']} ({time.time()-t0:.1f}s)", flush=True)
    for tol in (1e-9, 1e-8, 1e-7, 1e-10):
        try:
            yex = exact_dual(L, S['row_dual'], tol)
        except RuntimeError as ex:
            print('tol', tol, ex, flush=True)
            continue
        bad = []
        for r, v in yex.items():
            lo, hi = L['lo'][r], L['hi'][r]
            if lo != hi and np.isinf(hi) and v > 0:
                bad.append(r)
            if lo != hi and np.isinf(lo) and v < 0:
                bad.append(r)
        if bad:
            print(f"tol {tol}: {len(bad)} bad signs", flush=True)
            continue
        J, lam, nm = explicit_certificate(cfg, lat, L, yex, M, autos)
        json.dump(J, open(outfile, 'w'))
        if verbose:
            print(f"tol {tol}: support {len(yex)}, merges {nm}, lambda = {lam} = {float(lam):.12f} -> {outfile} "
                  f"({len(J['rows'])} rows, {time.time()-t0:.1f}s)", flush=True)
        return lam
    return None


if __name__ == '__main__':
    import pickle
    from eng2 import Lattice2
    from sweep2 import build
    job = json.loads(sys.argv[1])
    out = sys.argv[2]
    infos = pickle.load(open(sys.argv[3], 'rb'))['infos'] if len(sys.argv) > 3 else []
    c, ex, autos = build(job)
    lat = Lattice2(c, extra=ex, verbose=True, max_flats=job.get('max_flats', 400000))
    lam = certify(c, lat, job.get('M', 12), infos, autos, out, mg=job.get('mg', False), rshare=job.get('rshare', False),
                  rwmap=job.get('rwmap'))
    print('certified', lam, float(lam) if lam else None, flush=True)
