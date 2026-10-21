"""Numba separation for Matus four-variable cuts over a candidate set of flats."""
import numpy as np
import numba as nb
from numba import njit, prange


@njit(parallel=True, cache=True)
def _sep(h, J, F, s, tol, bv, ba, bb):
    nF = F.shape[0]
    cc = s * (s + 1) / 2.0
    for ic in prange(nF):
        c = F[ic]
        hc = h[c]
        for idd in range(nF):
            d = F[idd]
            hd = h[d]
            Icd = hc + hd - h[J[c, d]]
            best = 0.0
            barg_a = -1
            barg_b = -1
            for ia in range(nF):
                a = F[ia]
                ha = h[a]
                Jac = J[a, c]
                Jad = J[a, d]
                hJac = h[Jac]
                hJad = h[Jad]
                for ib in range(nF):
                    b = F[ib]
                    jab = J[a, b]
                    hab = h[jab]
                    hb = h[b]
                    Iab = ha + hb - hab
                    if Iab < tol:
                        continue
                    Jbc = J[b, c]
                    jabc = J[jab, c]
                    Iab_c = hJac + h[Jbc] - h[jabc] - hc
                    Iab_d = hJad + h[J[b, d]] - h[J[jab, d]] - hd
                    Ibc_a = hab + hJac - h[jabc] - ha
                    Iac_b = hab + h[Jbc] - h[jabc] - hb
                    val = Ibc_a + s * (-Iab + Iab_c + Iab_d + Icd) + cc * (Iac_b + Iab_c)
                    if val < best:
                        best = val
                        barg_a = a
                        barg_b = b
            bv[ic, idd] = best
            ba[ic, idd] = barg_a
            bb[ic, idd] = barg_b


def most_violated_nb(h, J, F, svals=(1, 2), top=300, tol=1e-7, threads=16):
    nb.set_num_threads(min(threads, nb.config.NUMBA_NUM_THREADS))
    F = np.asarray(F, dtype=np.int64)
    J = np.ascontiguousarray(J, dtype=np.int64)
    h = np.ascontiguousarray(h, dtype=np.float64)
    out = []
    nF = len(F)
    for s in svals:
        bv = np.zeros((nF, nF)); ba = np.full((nF, nF), -1, dtype=np.int64); bb = np.full((nF, nF), -1, dtype=np.int64)
        _sep(h, J, F, float(s), tol, bv, ba, bb)
        idx = np.argwhere(bv < -tol)
        for (ic, idd) in idx:
            out.append((float(bv[ic, idd]), s, int(ba[ic, idd]), int(bb[ic, idd]), int(F[ic]), int(F[idd])))
    out.sort()
    return out[:top]


def matus_val_vec(h, J, a, b, c, d, s):
    """Vectorized M_s over arrays a, b, c, d (flat ids, broadcastable)."""
    cc = s * (s + 1) / 2.0
    hab = h[J[a, b]]
    Iab = h[a] + h[b] - hab
    jac, jbc = J[a, c], J[b, c]
    jabc = J[J[a, b], c]
    Iab_c = h[jac] + h[jbc] - h[jabc] - h[c]
    Iab_d = h[J[a, d]] + h[J[b, d]] - h[J[J[a, b], d]] - h[d]
    Ibc_a = hab + h[jac] - h[jabc] - h[a]
    Iac_b = hab + h[jbc] - h[jabc] - h[b]
    Icd = h[c] + h[d] - h[J[c, d]]
    return Ibc_a + s * (-Iab + Iab_c + Iab_d + Icd) + cc * (Iac_b + Iab_c)


def refine(h, J, inst, allflats, sweeps=3, tol=1e-7):
    """Coordinate descent: from violated instances (v, s, a, b, c, d), replace one variable at a time by the
    best flat in allflats.  Returns improved instances (deduplicated)."""
    allf = np.asarray(allflats, dtype=np.int64)
    out = {}
    for (v, s, a, b, c, d) in inst:
        cur = [a, b, c, d]
        best = v
        for sw in range(sweeps):
            moved = False
            for pos in range(4):
                args = [np.full(len(allf), x, dtype=np.int64) for x in cur]
                args[pos] = allf
                vals = matus_val_vec(h, J, *args, s)
                k = int(np.argmin(vals))
                if vals[k] < best - 1e-12:
                    best = float(vals[k])
                    cur[pos] = int(allf[k])
                    moved = True
            if not moved:
                break
        if best < -tol:
            out[(s, *cur)] = best
    return sorted([(v, *k) for k, v in out.items()])


@njit(parallel=True, cache=True)
def _sep_alls(h, J, F, smax, tol, bv, ba, bb, bs):
    """One pass over (a,b,c,d) in F^4; for each quadruple pick the integer s in [1, smax] minimizing
    M_s = T1 + s*T2 + s(s+1)/2*T3 (T1 = I(b;c|a), T2 = Ingleton, T3 = I(a;c|b)+I(a;b|c) >= 0)."""
    nF = F.shape[0]
    for ic in prange(nF):
        c = F[ic]
        hc = h[c]
        for idd in range(nF):
            d = F[idd]
            hd = h[d]
            Icd = hc + hd - h[J[c, d]]
            best = 0.0
            barg_a = -1
            barg_b = -1
            barg_s = 0
            for ia in range(nF):
                a = F[ia]
                ha = h[a]
                Jac = J[a, c]
                Jad = J[a, d]
                hJac = h[Jac]
                hJad = h[Jad]
                for ib in range(nF):
                    b = F[ib]
                    jab = J[a, b]
                    hab = h[jab]
                    hb = h[b]
                    Iab = ha + hb - hab
                    if Iab < tol:
                        continue
                    Jbc = J[b, c]
                    jabc = J[jab, c]
                    Iab_c = hJac + h[Jbc] - h[jabc] - hc
                    Iab_d = hJad + h[J[b, d]] - h[J[jab, d]] - hd
                    T2 = -Iab + Iab_c + Iab_d + Icd
                    if T2 >= -tol:
                        continue
                    T1 = hab + hJac - h[jabc] - ha
                    T3 = (hab + h[Jbc] - h[jabc] - hb) + Iab_c
                    if T3 <= 1e-12:
                        s = smax
                    else:
                        s = int(-T2 / T3 - 0.5 + 0.5)
                        if s < 1:
                            s = 1
                        if s > smax:
                            s = smax
                    val = T1 + s * T2 + s * (s + 1) / 2.0 * T3
                    if s + 1 <= smax:
                        v2 = T1 + (s + 1) * T2 + (s + 1) * (s + 2) / 2.0 * T3
                        if v2 < val:
                            val = v2
                            s = s + 1
                    if s - 1 >= 1:
                        v3 = T1 + (s - 1) * T2 + (s - 1) * s / 2.0 * T3
                        if v3 < val:
                            val = v3
                            s = s - 1
                    if val < best:
                        best = val
                        barg_a = a
                        barg_b = b
                        barg_s = s
            bv[ic, idd] = best
            ba[ic, idd] = barg_a
            bb[ic, idd] = barg_b
            bs[ic, idd] = barg_s


def most_violated_alls(h, J, F, smax=64, top=400, tol=1e-7, threads=16):
    nb.set_num_threads(min(threads, nb.config.NUMBA_NUM_THREADS))
    F = np.asarray(F, dtype=np.int64)
    J = np.ascontiguousarray(J, dtype=np.int64)
    h = np.ascontiguousarray(h, dtype=np.float64)
    nF = len(F)
    bv = np.zeros((nF, nF)); ba = np.full((nF, nF), -1, dtype=np.int64)
    bb = np.full((nF, nF), -1, dtype=np.int64); bs = np.zeros((nF, nF), dtype=np.int64)
    _sep_alls(h, J, F, smax, tol, bv, ba, bb, bs)
    idx = np.argwhere(bv < -tol)
    out = [(float(bv[i, j]), int(bs[i, j]), int(ba[i, j]), int(bb[i, j]), int(F[i]), int(F[j])) for i, j in idx]
    out.sort()
    return out[:top]


def join_partial(lat, cand):
    """Jp[x, k] = cl(x u flat cand[k]) for every flat x (vectorized via the nxt table); col[f] = k or -1."""
    nxt = lat.nxt
    nf = lat.nflats
    Jp = np.empty((nf, len(cand)), dtype=np.int32)
    allx = np.arange(nf, dtype=np.int64)
    for k, y in enumerate(cand):
        cur = allx
        for e in lat.gens_of(y):
            cur = nxt[cur, e]
        Jp[:, k] = cur
    col = np.full(nf, -1, dtype=np.int64)
    col[np.asarray(cand, dtype=np.int64)] = np.arange(len(cand))
    return Jp, col


class PJ:
    """J[x, y] for y a candidate flat, backed by the partial table."""
    def __init__(self, Jp, col):
        self.Jp, self.col = Jp, col

    def __getitem__(self, xy):
        x, y = int(xy[0]), int(xy[1])
        k = self.col[y]
        if k < 0:
            raise KeyError("second argument must be a candidate flat")
        return int(self.Jp[x, k])


@njit(parallel=True, cache=True)
def _sep_alls_p(h, Jp, col, F, smax, tol, bv, ba, bb, bs):
    nF = F.shape[0]
    for ic in prange(nF):
        c = F[ic]
        kc = col[c]
        hc = h[c]
        for idd in range(nF):
            d = F[idd]
            kd = col[d]
            hd = h[d]
            Icd = hc + hd - h[Jp[c, kd]]
            best = 0.0
            barg_a = -1
            barg_b = -1
            barg_s = 0
            for ia in range(nF):
                a = F[ia]
                ha = h[a]
                Jac = Jp[a, kc]
                Jad = Jp[a, kd]
                hJac = h[Jac]
                hJad = h[Jad]
                for ib in range(nF):
                    b = F[ib]
                    jab = Jp[a, col[b]]
                    hab = h[jab]
                    hb = h[b]
                    Iab = ha + hb - hab
                    if Iab < tol:
                        continue
                    Jbc = Jp[b, kc]
                    jabc = Jp[jab, kc]
                    Iab_c = hJac + h[Jbc] - h[jabc] - hc
                    Iab_d = hJad + h[Jp[b, kd]] - h[Jp[jab, kd]] - hd
                    T2 = -Iab + Iab_c + Iab_d + Icd
                    if T2 >= -tol:
                        continue
                    T1 = hab + hJac - h[jabc] - ha
                    T3 = (hab + h[Jbc] - h[jabc] - hb) + Iab_c
                    if T3 <= 1e-12:
                        s = smax
                    else:
                        s = int(-T2 / T3)
                        if s < 1:
                            s = 1
                        if s > smax:
                            s = smax
                    val = T1 + s * T2 + s * (s + 1) / 2.0 * T3
                    if s + 1 <= smax:
                        v2 = T1 + (s + 1) * T2 + (s + 1) * (s + 2) / 2.0 * T3
                        if v2 < val:
                            val = v2
                            s = s + 1
                    if s - 1 >= 1:
                        v3 = T1 + (s - 1) * T2 + (s - 1) * s / 2.0 * T3
                        if v3 < val:
                            val = v3
                            s = s - 1
                    if val < best:
                        best = val
                        barg_a = a
                        barg_b = b
                        barg_s = s
            bv[ic, idd] = best
            ba[ic, idd] = barg_a
            bb[ic, idd] = barg_b
            bs[ic, idd] = barg_s


def most_violated_alls_p(h, Jp, col, F, smax=200, top=400, tol=1e-7, threads=16):
    nb.set_num_threads(min(threads, nb.config.NUMBA_NUM_THREADS))
    F = np.asarray(F, dtype=np.int64)
    h = np.ascontiguousarray(h, dtype=np.float64)
    nF = len(F)
    bv = np.zeros((nF, nF)); ba = np.full((nF, nF), -1, dtype=np.int64)
    bb = np.full((nF, nF), -1, dtype=np.int64); bs = np.zeros((nF, nF), dtype=np.int64)
    _sep_alls_p(h, Jp, col, F, smax, tol, bv, ba, bb, bs)
    idx = np.argwhere(bv < -tol)
    out = [(float(bv[i, j]), int(bs[i, j]), int(ba[i, j]), int(bb[i, j]), int(F[i]), int(F[j])) for i, j in idx]
    out.sort()
    return out[:top]
