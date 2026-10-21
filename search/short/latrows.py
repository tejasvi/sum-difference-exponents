"""Few-row certificates using lattice rows I(F;G|F^G) and monotone rows over flats.

usage: python latrows.py FORMS.json TARGET OUT.json [iters] [maxrank]
Rows: sm(F,G) = h(F) + h(G) - h(F v G) - h(F ^ G) >= 0 for incomparable flats F, G (F ^ G = intersection,
a flat), and mono(F,G) = h(F) - h(G) >= 0 for flats G < F.  Each row is expanded into elemental
check630 rows (chain rule; formal telescoping identity) with the same multiplier.
"""
import sys, json, time, itertools
from fractions import Fraction
import numpy as np
import scipy.sparse as sp
from scipy.optimize import linprog
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from eng import Lattice
from fastlp import build_lp, solve_lp
from kt import kt116
from cert_fast import exact_dual, check_signs, ref, fr


def build(forms):
    cfg = kt116()
    lat = Lattice(cfg, verbose=False, extra_amb=forms)
    L = build_lp(cfg, lat, verbose=False)
    return cfg, lat, L


def join(lat, F, G):
    f = F
    m = lat.masks[G]
    e = 0
    while m:
        if m & 1:
            f = int(lat.nxt[f, e])
        m >>= 1
        e += 1
    return f


def lattice_rows(lat, L, maxrank=None):
    colof = L['colof']
    masks = lat.masks
    nf = lat.nflats
    rank = lat.rank
    rows = {}     # key (sorted col-coef tuple) -> (kind, F, G)
    def add(vec, tag):
        d = {}
        for c, a in vec:
            if c >= 0:
                d[c] = d.get(c, 0) + a
        d = tuple(sorted((c, a) for c, a in d.items() if a != 0))
        if not d:
            return
        if d not in rows:
            rows[d] = tag
    t0 = time.time()
    for F in range(1, nf):
        for G in range(1, nf):
            if G == F:
                continue
            mF, mG = masks[F], masks[G]
            if (mF & mG) == mG:          # G subset F: monotone row
                add([(colof[F], 1), (colof[G], -1)], ('mono', F, G))
            elif F < G and (mF & mG) != mF:
                if maxrank is not None and max(rank[F], rank[G]) > maxrank:
                    continue
                M = lat.id_of[mF & mG]
                J = join(lat, F, G)
                add([(colof[F], 1), (colof[G], 1), (colof[J], -1), (colof[M], -1)], ('sm', F, G, J, M))
    print(f"  lattice rows: {len(rows)} distinct ({time.time()-t0:.1f}s)", flush=True)
    keys = list(rows.keys())
    tags = [rows[k] for k in keys]
    ri, rj, rv = [], [], []
    for i, k in enumerate(keys):
        for c, a in k:
            ri.append(i); rj.append(c); rv.append(a)
    A = sp.csr_matrix((rv, (ri, rj)), shape=(len(keys), L['ncol']))
    return A, tags


def make_L(L, Arows, tags):
    A0 = L['A'].tocsr()
    ci = list(range(L['ci_start'], L['ci_start'] + L['nci']))
    bs = list(range(L['bstart'], L['bstart'] + len(L['bflats'])))
    A = sp.vstack([Arows, A0[ci], A0[bs]]).tocsr()
    n = Arows.shape[0]
    lo = np.concatenate([np.zeros(n), np.zeros(len(ci)), np.full(len(bs), -np.inf)])
    hi = np.concatenate([np.full(n, np.inf), np.zeros(len(ci)), np.ones(len(bs))])
    L2 = dict(A=A, lo=lo, hi=hi, ncol=L['ncol'], nm=0, ns=n, nci=len(ci), ci_start=n,
              bstart=n + len(ci), xstart=n + len(ci), nx=0, obj_col=L['obj_col'], bflats=L['bflats'],
              tags=tags)
    return L2


def l1_support(L2, target, iters=10, eps=1e-6, tol=1e-9, cost=None, verbose=True):
    A = L2['A'].tocsr()
    n = L2['ns']
    nci = L2['nci']
    nb = len(L2['bflats'])
    Aeq = sp.hstack([A[:n].T, A[n:n + nci].T, -A[n + nci:].T]).tocsc()
    beq = np.zeros(L2['ncol'])
    beq[L2['obj_col']] = -1.0
    nv = n + nci + nb
    Aub = np.zeros((1, nv)); Aub[0, n + nci:] = 1.0
    bounds = [(0, None)] * n + [(None, None)] * nci + [(0, None)] * nb
    w = np.ones(n) if cost is None else cost.copy()
    best = None
    for it in range(iters):
        c = np.zeros(nv); c[:n] = w
        res = linprog(c, A_ub=Aub, b_ub=[float(target)], A_eq=Aeq, b_eq=beq, bounds=bounds, method='highs')
        if res.status != 0:
            raise RuntimeError(res.message)
        mu = res.x[:n]
        supp = np.nonzero(mu > tol)[0]
        if verbose:
            print(f"  iter {it}: support {len(supp)}", flush=True)
        if best is None or len(supp) < len(best):
            best = supp
        w = (1.0 if cost is None else cost) / (mu + eps)
    return best


def restricted(L2, supp):
    lo = L2['lo'].copy(); hi = L2['hi'].copy()
    n = L2['ns']
    keep = np.zeros(n, dtype=bool); keep[supp] = True
    lo[:n][~keep] = -np.inf; hi[:n][~keep] = np.inf
    L3 = dict(L2); L3['lo'] = lo; L3['hi'] = hi
    S = solve_lp(L3, opts={"solver": "simplex"})
    yex = exact_dual(L3, S, verbose=False)
    bad = check_signs(L3, yex)
    if bad:
        raise RuntimeError(f"bad signs {bad[:3]}")
    return S, yex


def flat_gens(lat, F, base=0):
    """Elements e1..ek (E indices) with cl(base + e1..ek) = F, greedy via nxt."""
    cur = base
    out = []
    m = lat.masks[F]
    e = 0
    while cur != F:
        # pick the smallest-index element of F not in cur
        mc = lat.masks[cur]
        cand = [i for i in range(lat.m) if (m >> i) & 1 and not (mc >> i) & 1]
        # prefer standard forms (lower index) first
        i = cand[0]
        out.append(i)
        cur = int(lat.nxt[cur, i])
    return out


def to_json(cfg, lat, L, L2, yex):
    rows_out = []
    lam = {}
    grouped = []
    n = L2['ns']
    for i, v in sorted(yex.items()):
        if v == 0:
            continue
        if i < n:
            mult = -v
            tag = L2['tags'][i]
            if tag[0] == 'mono':
                _, F, G = tag
                gG = flat_gens(lat, G)
                fs = flat_gens(lat, F, base=G)
                K = [ref(lat.rep(e)) for e in gG]
                for e in fs:
                    rows_out.append(dict(type='mono', K=list(K), i=ref(lat.rep(e)), mult=fr(mult)))
                    K = K + [ref(lat.rep(e))]
                grouped.append(dict(kind='mono', F=F, G=G, mult=mult, nelem=len(fs)))
            else:
                _, F, G, J, M = tag
                gM = flat_gens(lat, M)
                fs = flat_gens(lat, F, base=M)
                gs = flat_gens(lat, G, base=M)
                Kb = [ref(lat.rep(e)) for e in gM]
                cnt = 0
                for a in range(len(fs)):
                    for b in range(len(gs)):
                        K = Kb + [ref(lat.rep(e)) for e in fs[:a]] + [ref(lat.rep(e)) for e in gs[:b]]
                        rows_out.append(dict(type='sub', K=K, i=ref(lat.rep(fs[a])), j=ref(lat.rep(gs[b])),
                                             mult=fr(mult)))
                        cnt += 1
                grouped.append(dict(kind='sm', F=F, G=G, J=J, M=M, mult=mult, nelem=cnt))
        elif i < n + L2['nci']:
            rows_out.append(dict(type='ci', step=int(i - n), mult=fr(-v)))
            grouped.append(dict(kind='ci', step=int(i - n), mult=-v))
        else:
            s = cfg.R[i - L2['bstart']]
            lam[f"{s[0]},{s[1]}"] = fr(v)
    eqlaw = [dict(step=int(t), gens=[ref(g) for g in gF]) for (F, G, t, gF) in L['eqp']]
    steps = [dict(U=[int(u) for u in U], V=[ref(g) for g in V]) for (U, V, nid) in cfg.steps]
    J = dict(slopes=[list(s) for s in cfg.R], steps=steps, extra=[list(map(int, f)) for f in lat.extra_amb],
             eqlaw=eqlaw, rows=rows_out)
    J['lambda'] = lam
    tot = sum(Fraction(x) for x in lam.values())
    J['claimed_C'] = fr(tot)
    return J, tot, grouped


if __name__ == '__main__':
    forms = json.load(open(sys.argv[1]))
    target = Fraction(sys.argv[2])
    out = sys.argv[3]
    iters = int(sys.argv[4]) if len(sys.argv) > 4 else 10
    maxrank = int(sys.argv[5]) if len(sys.argv) > 5 else None
    t0 = time.time()
    cfg, lat, L = build(forms)
    Arows, tags = lattice_rows(lat, L, maxrank)
    L2 = make_L(L, Arows, tags)
    print(f"built: {lat.nflats} flats, {L['ncol']} cols, {Arows.shape[0]} lattice rows, {time.time()-t0:.1f}s", flush=True)
    supp = l1_support(L2, target, iters=iters)
    S, yex = restricted(L2, supp)
    J, tot, grouped = to_json(cfg, lat, L, L2, yex)
    json.dump(J, open(out, 'w'))
    import pickle
    pickle.dump(dict(grouped=grouped, masks=lat.masks, E=lat.E, idx=lat.idx, nflats=lat.nflats,
                     extra=lat.extra_amb, eqp=[(F, G, t) for (F, G, t, g) in L['eqp']]),
                open(out.replace('.json', '.pkl'), 'wb'))
    from collections import Counter
    print(f"CERT {out}: C = {tot} = {float(tot):.12f}; grouped rows {len(grouped)} "
          f"{dict(Counter(g['kind'] for g in grouped))}; elemental rows {len(J['rows'])}", flush=True)
