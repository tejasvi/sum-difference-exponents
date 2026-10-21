"""Cutting-plane test: add Zhang-Yeung / Matus four-variable inequalities over flats to a scheme's LP.

Matus family (Matus 2007; cf. Kleinwaks Remark 3.? and Csirmaz-Csirmaz): for s >= 1,
  M_s(a,b,c,d) = I(b;c|a) + s*[abcd] + s(s+1)/2 * (I(a;c|b) + I(a;b|c)) >= 0,
  [abcd] = -I(a;b) + I(a;b|c) + I(a;b|d) + I(c;d)   (Ingleton expression).
s = 1 is (a permutation of) the Zhang-Yeung inequality.  Each of a, b, c, d is a flat (joint variable).
"""
import sys, time
import numpy as np
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from eng import Lattice
from fastlp import build_lp, solve_lp


def join_table(lat):
    nf = lat.nflats
    gens = [lat.gens_of(f) for f in range(nf)]
    J = np.zeros((nf, nf), dtype=np.int64)
    for F in range(nf):
        for G in range(nf):
            f = F
            for e in gens[G]:
                f = int(lat.nxt[f, e])
            J[F, G] = f
    return J


def h_values(L, S, lat):
    colof = L['colof']
    xv = S['col_value']
    h = np.where(colof >= 0, xv[np.maximum(colof, 0)], 0.0)
    return h


def matus_terms(J, a, b, c, d, s):
    """Return list of (flat, coef) for M_s(a,b,c,d) (>= 0)."""
    t = {}

    def add(f, k):
        t[f] = t.get(f, 0) + k

    def I(x, y, z=None):  # I(x;y|z) = h(xz)+h(yz)-h(xyz)-h(z)
        if z is None:
            return [(x, 1), (y, 1), (J[x, y], -1)]
        return [(J[x, z], 1), (J[y, z], 1), (J[J[x, y], z], -1), (z, -1)]

    terms = []
    terms += [(f, k) for f, k in I(b, c, a)]
    ing = [(f, -k) for f, k in I(a, b)] + I(a, b, c) + I(a, b, d) + I(c, d)
    terms += [(f, s * k) for f, k in ing]
    cc = s * (s + 1) // 2
    terms += [(f, cc * k) for f, k in I(a, c, b) + I(a, b, c)]
    for f, k in terms:
        add(int(f), k)
    return {f: k for f, k in t.items() if k != 0 and f != 0}


def most_violated(h, J, svals=(1, 2, 3), top=200, flats=None, tol=1e-7):
    """Vectorized search over (a,b,c,d) in flats^4 for violated M_s; returns list of (viol, s, a, b, c, d)."""
    nf = len(h)
    F = np.arange(nf) if flats is None else np.array(flats)
    out = []
    hh = h
    # precompute pairwise
    for s in svals:
        cc = s * (s + 1) / 2
        for ci, c in enumerate(F):
            for d in F:
                # Ingleton part I(c;d) independent of a,b
                Icd = hh[c] + hh[d] - hh[J[c, d]]
                # vectors over a, b in F
                A = F[:, None]
                B = F[None, :]
                hab = hh[J[A, B]]
                Iab = hh[A] + hh[B] - hab
                Jac = J[A, c]; Jbc = J[B, c]; Jabc = J[J[A, B], c]
                Iab_c = hh[Jac] + hh[Jbc] - hh[Jabc] - hh[c]
                Jad = J[A, d]; Jbd = J[B, d]; Jabd = J[J[A, B], d]
                Iab_d = hh[Jad] + hh[Jbd] - hh[Jabd] - hh[d]
                # I(b;c|a) = h(ab)+h(ac)-h(abc)-h(a)
                Ibc_a = hab + hh[Jac] - hh[Jabc] - hh[A]
                # I(a;c|b) = h(ab)+h(bc)-h(abc)-h(b)
                Iac_b = hab + hh[Jbc] - hh[Jabc] - hh[B]
                val = Ibc_a + s * (-Iab + Iab_c + Iab_d + Icd) + cc * (Iac_b + Iab_c)
                idx = np.argwhere(val < -tol)
                for (i, j) in idx:
                    out.append((float(val[i, j]), s, int(F[i]), int(F[j]), int(c), int(d)))
    out.sort()
    return out[:top]


def cutting_plane(cfg, rounds=int(__import__("os").environ.get("NS_ROUNDS", "20")), svals=(1, 2, 3), top=200, verbose=True):
    lat = Lattice(cfg, verbose=False)
    J = join_table(lat)
    extra = []
    for it in range(rounds):
        L = build_lp(cfg, lat, extra_rows=[(dct, 0.0, np.inf) for dct in extra])
        S = solve_lp(L)
        h = h_values(L, S, lat)
        viol = most_violated(h, J, svals, top)
        if verbose:
            print(f"round {it}: LP {S['value']:.9f}  extra rows {len(extra)}  violated found {len(viol)}"
                  f"  worst {viol[0][0] if viol else 0:.3e}", flush=True)
        if not viol:
            break
        seen = set(tuple(sorted(d.items())) for d in extra)
        for (v, s, a, b, c, d) in viol:
            dct = matus_terms(J, a, b, c, d, s)
            key = tuple(sorted(dct.items()))
            if key not in seen:
                seen.add(key)
                extra.append(dct)
    return S['value'], extra, lat


if __name__ == '__main__':
    from kt import kt116, kt74
    which = sys.argv[1] if len(sys.argv) > 1 else '116'
    cfg = kt116() if which == '116' else kt74()
    t0 = time.time()
    v, extra, lat = cutting_plane(cfg)
    print('final', v, len(extra), f'{time.time()-t0:.1f}s')
