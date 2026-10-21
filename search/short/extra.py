"""Extra cross-vertex linear forms for a configuration: small integer combinations of an L-basis of
ambient coordinates (chosen greedily among x_v, y_v)."""
import itertools
from eng import rank_q


def coord_basis(cfg):
    B, E, idx = cfg.standard_forms()
    basis, rows = [], []
    for v in range(cfg.n):
        for c in (0, 1):
            f = [0] * (2 * cfg.n)
            f[2 * v + c] = 1
            r = cfg.coords(B, f)
            if rank_q(rows + [r]) > len(rows):
                rows.append(r)
                basis.append(f)
    return basis


def extra_forms(cfg, coeffs=(-1, 0, 1), maxnz=3, basis=None):
    if basis is None:
        basis = coord_basis(cfg)
    out = []
    nzc = [c for c in coeffs if c != 0]
    for nz in range(1, maxnz + 1):
        for S in itertools.combinations(range(len(basis)), nz):
            for cs in itertools.product(nzc, repeat=nz):
                if cs[0] < 0:
                    continue  # projective: first coefficient positive
                f = [0] * (2 * cfg.n)
                for i, c in zip(S, cs):
                    f = [a + c * b for a, b in zip(f, basis[i])]
                out.append(f)
    return out


def extra_forms_split(cfg, k_old, coeffs=(-1, 1), nz_old=3, nz_new=2):
    """Forms on the first k_old basis coordinates with <= nz_old nonzeros, plus forms involving the
    remaining (new) coordinates with <= nz_new nonzeros in total."""
    basis = coord_basis(cfg)
    old, new = basis[:k_old], basis[k_old:]
    out = extra_forms(cfg, coeffs, nz_old, basis=old)
    nzc = [c for c in coeffs if c != 0]
    allb = old + new
    nb = len(allb)
    for nz in range(1, nz_new + 1):
        for S in itertools.combinations(range(nb), nz):
            if not any(i >= k_old for i in S):
                continue
            for cs in itertools.product(nzc, repeat=nz):
                if cs[0] < 0:
                    continue
                f = [0] * (2 * cfg.n)
                for i, c in zip(S, cs):
                    f = [a + c * b for a, b in zip(f, allb[i])]
                out.append(f)
    return out
