"""Dougherty-Freiling-Zeger four-variable non-Shannon inequalities (arXiv:1104.3602, Section VIII list of 214),
each of the form
  a I(A;B) <= b I(A;B|C) + c I(A;C|B) + d I(B;C|A) + e I(A;B|D) + f I(A;D|B) + g I(B;D|A) + h I(C;D) + i I(C;D|A),
applied to flats (joint variables) A, B, C, D.  Separation over ordered quadruples of candidate flats (partial join
table, as in sepnb), restricted to Ingleton-violating quadruples (every listed inequality has b, e, h >= a, so it
holds whenever the Ingleton expression is >= 0)."""
import json, os
import numpy as np
import numba as nb
from numba import njit, prange

HERE = os.path.dirname(os.path.abspath(__file__))


def load_dfz(path=None, proven_only=True):
    """(ids, W): by default only the entries with an exact copy-lemma proof in dfz/lemmas.json (192 of 214; the
    other 22 were not derived with our encoding of their listed copy steps and are not used)."""
    E = json.load(open(path or os.path.join(HERE, 'dfz', 'dfz214_raw.json')))
    ks = sorted(int(k) for k in E)
    if proven_only:
        P = json.load(open(os.path.join(HERE, 'dfz', 'lemmas.json')))
        ks = [k for k in ks if str(k) in P]
    return ks, np.array([E[str(k)] for k in ks], dtype=np.float64)


def dfz_terms(J, a, b, c, d, w):
    """{flat: coef} of  b I(A;B|C) + ... + i I(C;D|A) - a I(A;B)  (>= 0), w = 9 integers."""
    t = {}

    def I(x, y, z=None):
        if z is None:
            return [(x, 1), (y, 1), (J[x, y], -1)]
        return [(J[x, z], 1), (J[y, z], 1), (J[J[x, y], z], -1), (z, -1)]

    parts = [(-w[0], I(a, b)), (w[1], I(a, b, c)), (w[2], I(a, c, b)), (w[3], I(b, c, a)), (w[4], I(a, b, d)),
             (w[5], I(a, d, b)), (w[6], I(b, d, a)), (w[7], I(c, d)), (w[8], I(c, d, a))]
    for k, terms in parts:
        if k == 0:
            continue
        for f, s in terms:
            f = int(f)
            t[f] = t.get(f, 0) + int(k) * s
    return {f: k for f, k in t.items() if k != 0 and f != 0}


@njit(parallel=True, cache=True)
def _sep_dfz_p(h, Jp, col, F, W, tol, bv, ba, bb, bk):
    nF = F.shape[0]
    K = W.shape[0]
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
            barg_k = -1
            for ia in range(nF):
                a = F[ia]
                ha = h[a]
                Jac = Jp[a, kc]
                Jad = Jp[a, kd]
                hJac = h[Jac]
                hJad = h[Jad]
                Icd_a = hJac + hJad - ha - h[Jp[Jac, kd]]
                for ib in range(nF):
                    b = F[ib]
                    jab = Jp[a, col[b]]
                    hab = h[jab]
                    hb = h[b]
                    Iab = ha + hb - hab
                    if Iab < tol:
                        continue
                    Jbc = Jp[b, kc]
                    Jbd = Jp[b, kd]
                    hjabc = h[Jp[jab, kc]]
                    hjabd = h[Jp[jab, kd]]
                    Iab_c = hJac + h[Jbc] - hjabc - hc
                    Iab_d = hJad + h[Jbd] - hjabd - hd
                    if -Iab + Iab_c + Iab_d + Icd >= -tol:
                        continue
                    Iac_b = hab + h[Jbc] - hb - hjabc
                    Ibc_a = hab + hJac - ha - hjabc
                    Iad_b = hab + h[Jbd] - hb - hjabd
                    Ibd_a = hab + hJad - ha - hjabd
                    for k in range(K):
                        val = (-W[k, 0] * Iab + W[k, 1] * Iab_c + W[k, 2] * Iac_b + W[k, 3] * Ibc_a
                               + W[k, 4] * Iab_d + W[k, 5] * Iad_b + W[k, 6] * Ibd_a + W[k, 7] * Icd
                               + W[k, 8] * Icd_a) / W[k, 0]
                        if val < best:
                            best = val
                            barg_a = a
                            barg_b = b
                            barg_k = k
            bv[ic, idd] = best
            ba[ic, idd] = barg_a
            bb[ic, idd] = barg_b
            bk[ic, idd] = barg_k


def most_violated_dfz_p(h, Jp, col, F, W, top=400, tol=1e-7, threads=16):
    """Returns sorted list of (normalized violation, k, a, b, c, d); k indexes the rows of W."""
    nb.set_num_threads(min(threads, nb.config.NUMBA_NUM_THREADS))
    F = np.asarray(F, dtype=np.int64)
    h = np.ascontiguousarray(h, dtype=np.float64)
    W = np.ascontiguousarray(W, dtype=np.float64)
    nF = len(F)
    bv = np.zeros((nF, nF)); ba = np.full((nF, nF), -1, dtype=np.int64)
    bb = np.full((nF, nF), -1, dtype=np.int64); bk = np.full((nF, nF), -1, dtype=np.int64)
    _sep_dfz_p(h, Jp, col, F, W, tol, bv, ba, bb, bk)
    idx = np.argwhere(bv < -tol)
    out = [(float(bv[i, j]), int(bk[i, j]), int(ba[i, j]), int(bb[i, j]), int(F[i]), int(F[j])) for i, j in idx]
    out.sort()
    return out[:top]


@njit(parallel=True, cache=True)
def _sep_dfz_p2(h, Jp, col, Fab, Fcd, W, tol, bv, ba, bb, bk):
    """As _sep_dfz_p with a, b ranging over Fab and c, d over Fcd (every flat of Fab u Fcd must be a column of Jp)."""
    nA = Fab.shape[0]
    nC = Fcd.shape[0]
    K = W.shape[0]
    for ic in prange(nC):
        c = Fcd[ic]
        kc = col[c]
        hc = h[c]
        for idd in range(nC):
            d = Fcd[idd]
            kd = col[d]
            hd = h[d]
            Icd = hc + hd - h[Jp[c, kd]]
            best = 0.0
            barg_a = -1
            barg_b = -1
            barg_k = -1
            for ia in range(nA):
                a = Fab[ia]
                ha = h[a]
                Jac = Jp[a, kc]
                Jad = Jp[a, kd]
                hJac = h[Jac]
                hJad = h[Jad]
                Icd_a = hJac + hJad - ha - h[Jp[Jac, kd]]
                for ib in range(nA):
                    b = Fab[ib]
                    jab = Jp[a, col[b]]
                    hab = h[jab]
                    hb = h[b]
                    Iab = ha + hb - hab
                    if Iab < tol:
                        continue
                    Jbc = Jp[b, kc]
                    Jbd = Jp[b, kd]
                    hjabc = h[Jp[jab, kc]]
                    hjabd = h[Jp[jab, kd]]
                    Iab_c = hJac + h[Jbc] - hjabc - hc
                    Iab_d = hJad + h[Jbd] - hjabd - hd
                    if -Iab + Iab_c + Iab_d + Icd >= -tol:
                        continue
                    Iac_b = hab + h[Jbc] - hb - hjabc
                    Ibc_a = hab + hJac - ha - hjabc
                    Iad_b = hab + h[Jbd] - hb - hjabd
                    Ibd_a = hab + hJad - ha - hjabd
                    for k in range(K):
                        val = (-W[k, 0] * Iab + W[k, 1] * Iab_c + W[k, 2] * Iac_b + W[k, 3] * Ibc_a
                               + W[k, 4] * Iab_d + W[k, 5] * Iad_b + W[k, 6] * Ibd_a + W[k, 7] * Icd
                               + W[k, 8] * Icd_a) / W[k, 0]
                        if val < best:
                            best = val
                            barg_a = a
                            barg_b = b
                            barg_k = k
            bv[ic, idd] = best
            ba[ic, idd] = barg_a
            bb[ic, idd] = barg_b
            bk[ic, idd] = barg_k


def most_violated_dfz_p2(h, Jp, col, Fab, Fcd, W, top=400, tol=1e-7, threads=16):
    nb.set_num_threads(min(threads, nb.config.NUMBA_NUM_THREADS))
    Fab = np.asarray(Fab, dtype=np.int64)
    Fcd = np.asarray(Fcd, dtype=np.int64)
    h = np.ascontiguousarray(h, dtype=np.float64)
    W = np.ascontiguousarray(W, dtype=np.float64)
    nC = len(Fcd)
    bv = np.zeros((nC, nC)); ba = np.full((nC, nC), -1, dtype=np.int64)
    bb = np.full((nC, nC), -1, dtype=np.int64); bk = np.full((nC, nC), -1, dtype=np.int64)
    _sep_dfz_p2(h, Jp, col, Fab, Fcd, W, tol, bv, ba, bb, bk)
    idx = np.argwhere(bv < -tol)
    out = [(float(bv[i, j]), int(bk[i, j]), int(ba[i, j]), int(bb[i, j]), int(Fcd[i]), int(Fcd[j])) for i, j in idx]
    out.sort()
    return out[:top]
