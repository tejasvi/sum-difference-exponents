"""Vectorized LP construction for the entropy LP (same rows as eng.build_and_solve)."""
import sys, time
import numpy as np
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from eng import UF, equal_law_pairs, ci_rows


def shannon_arrays(lat):
    nxt = lat.nxt
    nf, m = nxt.shape
    A, B, J, K = [], [], [], []
    MA, MK = [], []
    for k in range(nf):
        row = nxt[k]
        u, first = np.unique(row, return_index=True)
        sel = u != k
        cov = u[sel]
        rep = first[sel]
        if cov.size == 0:
            continue
        MA.append(cov)
        MK.append(np.full(cov.size, k))
        if cov.size < 2:
            continue
        Jm = nxt[cov[:, None], rep[None, :]]          # Jm[i, j] = cl(cov_i + rep_j)
        ii, jj = np.triu_indices(cov.size, 1)
        jv = Jm[ii, jj]
        ok = (jv != cov[ii]) & (jv != cov[jj])
        if ok.any():
            A.append(cov[ii[ok]])
            B.append(cov[jj[ok]])
            J.append(jv[ok])
            K.append(np.full(int(ok.sum()), k))
    cat = lambda L: np.concatenate(L) if L else np.zeros(0, dtype=np.int64)
    return cat(MA), cat(MK), cat(A), cat(B), cat(J), cat(K)


def build_lp(cfg, lat, verbose=False, extra_rows=None):
    """Returns dict with scipy CSR matrix, bounds, tags, class map."""
    import scipy.sparse as sp
    t0 = time.time()
    eqp = equal_law_pairs(cfg, lat, verbose=False)
    uf = UF(lat.nflats)
    for (F, G, t, g) in eqp:
        uf.union(F, G)
    cls = np.array([uf.find(i) for i in range(lat.nflats)], dtype=np.int64)
    zc = cls[0]
    uniq = np.unique(cls)
    uniq = uniq[uniq != zc]
    colof = np.full(lat.nflats, -1, dtype=np.int64)
    pos = {c: i for i, c in enumerate(uniq)}
    for c, i in pos.items():
        colof[cls == c] = i
    colof[cls == zc] = -1
    ncol = len(uniq)
    MA, MK, A, B, J, K = shannon_arrays(lat)
    # monotone rows: +col(MA) - col(MK)
    ca, ck = colof[MA], colof[MK]
    keep = ca != ck
    mono = np.stack([ca[keep], ck[keep]], 1)
    mono_tag = np.stack([MA[keep], MK[keep]], 1)
    mono, mi = np.unique(mono, axis=0, return_index=True)
    mono_tag = mono_tag[mi]
    # sub rows: +A +B -J -K, cancel equal classes
    p = np.sort(np.stack([colof[A], colof[B]], 1), 1)
    q = np.sort(np.stack([colof[J], colof[K]], 1), 1)
    sub_tag = np.stack([A, B, J, K], 1)
    rowsP = p.copy()
    rowsQ = q.copy()
    # cancellation: for each pos entry equal to a neg entry remove both (handle up to 2 matches)
    for i in range(2):
        for j in range(2):
            mt = (rowsP[:, i] == rowsQ[:, j]) & (rowsP[:, i] != -2)
            rowsP[mt, i] = -2
            rowsQ[mt, j] = -2
    # -1 means empty-set class (zero), -2 cancelled: both dropped
    key = np.concatenate([np.sort(rowsP, 1), np.sort(rowsQ, 1)], 1)
    nontriv = ~np.all(np.isin(key, [-1, -2]), axis=1)
    key, sub_tag = key[nontriv], sub_tag[nontriv]
    key, si = np.unique(key, axis=0, return_index=True)
    sub_tag = sub_tag[si]
    rows_i, rows_j, rows_v = [], [], []
    lo, hi, tags = [], [], []
    r = 0
    INF = np.inf
    # mono
    nm = len(mono)
    if nm:
        ar = np.arange(nm)
        ok0 = mono[:, 0] >= 0
        ok1 = mono[:, 1] >= 0
        rows_i += [ar[ok0], ar[ok1]]
        rows_j += [mono[ok0, 0], mono[ok1, 1]]
        rows_v += [np.ones(int(ok0.sum())), -np.ones(int(ok1.sum()))]
        r = nm
    lo += [0.0] * nm
    hi += [INF] * nm
    # sub
    ns = len(key)
    if ns:
        idx = np.arange(r, r + ns)
        for c, sgn in [(0, 1.0), (1, 1.0), (2, -1.0), (3, -1.0)]:
            colv = key[:, c]
            ok = colv >= 0
            rows_i.append(idx[ok])
            rows_j.append(colv[ok])
            rows_v.append(np.full(int(ok.sum()), sgn))
        r += ns
    lo += [0.0] * ns
    hi += [INF] * ns
    # ci rows
    ci = ci_rows(cfg, lat)
    ci_start = r
    for t, row in enumerate(ci):
        d = {}
        for f, a in row:
            c = colof[f]
            if c >= 0:
                d[c] = d.get(c, 0) + a
        d = {c: a for c, a in d.items() if a != 0}
        rows_i.append(np.full(len(d), r))
        rows_j.append(np.array(list(d.keys()), dtype=np.int64))
        rows_v.append(np.array(list(d.values()), dtype=float))
        lo.append(0.0)
        hi.append(0.0)
        r += 1
    nci = len(ci)
    # extra rows: list of (dict flat->coef, lo, hi)
    xstart = r
    if extra_rows:
        for (dct, l, h) in extra_rows:
            d = {}
            for f, a in dct.items():
                c = colof[f]
                if c >= 0:
                    d[c] = d.get(c, 0) + a
            d = {c: a for c, a in d.items() if a != 0}
            if not d:
                raise RuntimeError("empty extra row")
            rows_i.append(np.full(len(d), r))
            rows_j.append(np.array(list(d.keys()), dtype=np.int64))
            rows_v.append(np.array(list(d.values()), dtype=float))
            lo.append(l)
            hi.append(h)
            r += 1
    nx = r - xstart
    # bounds
    bstart = r
    bflats = []
    for s in cfg.R:
        f = lat.cl_gens([(0, s)])
        bflats.append(f)
        rows_i.append(np.array([r]))
        rows_j.append(np.array([colof[f]]))
        rows_v.append(np.array([1.0]))
        lo.append(-INF)
        hi.append(1.0)
        r += 1
    obj_f = lat.cl_gens([(0, (1, 0)), (0, (0, 1))])
    Amat = sp.csr_matrix((np.concatenate(rows_v), (np.concatenate(rows_i), np.concatenate(rows_j))),
                         shape=(r, ncol))
    if verbose:
        print(f"  LP: {ncol} cols, {r} rows (mono {nm}, sub {ns}, ci {nci}), {time.time()-t0:.2f}s",
              flush=True)
    return dict(A=Amat, lo=np.array(lo), hi=np.array(hi), ncol=ncol, nm=nm, ns=ns, nci=nci,
                mono_tag=mono_tag, sub_tag=sub_tag, ci_start=ci_start, bstart=bstart,
                xstart=xstart, nx=nx, obj_col=int(colof[obj_f]), colof=colof, cls=cls, eqp=eqp,
                bflats=bflats)


def solve_lp(L, verbose=False, opts=None):
    import highspy
    h = highspy.Highs()
    h.setOptionValue("output_flag", False)
    if opts:
        for k, v in opts.items():
            h.setOptionValue(k, v)
    A = L['A']
    lp = highspy.HighsLp()
    lp.num_col_ = L['ncol']
    lp.num_row_ = A.shape[0]
    c = np.zeros(L['ncol'])
    c[L['obj_col']] = 1.0
    lp.col_cost_ = c
    INF = highspy.kHighsInf
    lp.col_lower_ = np.full(L['ncol'], -INF)
    lp.col_upper_ = np.full(L['ncol'], INF)
    lo = L['lo'].copy()
    hi = L['hi'].copy()
    lo[np.isinf(lo)] = -INF
    hi[np.isinf(hi)] = INF
    lp.row_lower_ = lo
    lp.row_upper_ = hi
    lp.a_matrix_.format_ = highspy.MatrixFormat.kRowwise
    lp.a_matrix_.start_ = A.indptr.astype(np.int32)
    lp.a_matrix_.index_ = A.indices.astype(np.int32)
    lp.a_matrix_.value_ = A.data.astype(float)
    lp.a_matrix_.num_col_ = L['ncol']
    lp.a_matrix_.num_row_ = A.shape[0]
    lp.sense_ = highspy.ObjSense.kMaximize
    h.passModel(lp)
    h.run()
    st = h.modelStatusToString(h.getModelStatus())
    val = h.getInfo().objective_function_value
    sol = h.getSolution()
    rd = np.array(sol.row_dual)
    lam = rd[L['bstart']:L['bstart'] + len(L['bflats'])]
    out = dict(value=val, status=st, row_dual=rd, col_value=np.array(sol.col_value), lam=lam,
               row_value=np.array(sol.row_value))
    try:
        b = h.getBasis()
        if b.valid:
            out['row_basic'] = np.array([str(x).endswith('kBasic') for x in b.row_status])
    except Exception:
        pass
    return out


def evaluate_cfg(cfg, max_flats=100000, verbose=False, extra=None):
    from eng import Lattice
    lat = Lattice(cfg, verbose=False, max_flats=max_flats)
    L = build_lp(cfg, lat, verbose=verbose, extra_rows=extra(lat) if extra else None)
    S = solve_lp(L, verbose=verbose)
    return S, L, lat
