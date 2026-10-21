"""Exact certificate extraction for LPs built by fastlp.build_lp (supports extra forms).

Certificate JSON fields:
  slopes, steps (copy steps {U, V} or link steps {link: [U, u, w, link]}), extra (ambient integer vectors),
  lambda, eqlaw (step, gens), rows (sub/mono with K, i, j as form refs; ci with step), claimed_C.
Form refs: [v, [a, b]] = standard form a x_v + b y_v;  ["amb", k] = extra form k.
"""
import json, sys, time
from fractions import Fraction
import numpy as np
import flint


def fr(x):
    return f"{x.numerator}/{x.denominator}"


def ref(g):
    if g[0] == 'amb':
        return ["amb", int(g[1])]
    v, s = g
    return [int(v), [int(s[0]), int(s[1])]]


def exact_dual(L, S, tol=1e-9, verbose=True):
    A = L['A'].tocsr()
    y = S['row_dual']
    ncol = L['ncol']
    supp = np.nonzero(np.abs(y) > tol)[0]
    sub = A[supp]
    # touched columns
    cols = np.unique(sub.indices)
    obj = L['obj_col']
    if obj not in set(cols.tolist()):
        cols = np.unique(np.concatenate([cols, [obj]]))
    cpos = {c: i for i, c in enumerate(cols)}
    nr, nc = len(cols), len(supp)
    if verbose:
        print(f"  dual support {nc} rows, {nr} touched columns", flush=True)
    # matrix Mt (nr x nc): Mt[col, j] = A[supp[j], col]
    rows_list = [[0] * (nc + 1) for _ in range(nr)]
    subc = sub.tocoo()
    for j, c, v in zip(subc.row, subc.col, subc.data):
        rows_list[cpos[c]][j] = int(round(v))
    rows_list[cpos[obj]][nc] = 1
    t0 = time.time()
    M = flint.fmpq_mat(rows_list)
    R, rank = M.rref()
    if verbose:
        print(f"  rref {nr}x{nc+1} rank {rank} in {time.time()-t0:.1f}s", flush=True)
    # read pivots
    piv = []
    r = 0
    for c in range(nc + 1):
        if r < rank and R[r, c] != 0:
            piv.append(c)
            r += 1
    if nc in piv:
        raise RuntimeError("inconsistent: objective not in span of support rows")
    # free variables: rounded float duals; pivot variables solved exactly
    pset = set(piv)
    free = [c for c in range(nc) if c not in pset]
    yfree = {c: Fraction(float(y[supp[c]])).limit_denominator(10**6) for c in free}
    if verbose and free:
        print(f"  {len(free)} free support variables (dependent rows); fixed to rounded floats", flush=True)
    yex = {}
    for c, v in yfree.items():
        if v != 0:
            yex[int(supp[c])] = v
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


def check_signs(L, yex):
    nm, ns, nci = L['nm'], L['ns'], L['nci']
    bad = []
    for i, v in yex.items():
        if i < nm + ns:
            if v > 0:
                bad.append((i, v))
        elif L['bstart'] <= i:
            if v < 0:
                bad.append((i, v))
        elif L['xstart'] <= i < L['xstart'] + L['nx']:
            if v > 0:
                bad.append((i, v))
    return bad


def to_json(cfg, lat, L, yex, extra_defs=None):
    nm, ns = L['nm'], L['ns']
    out_rows, lam = [], {}
    gens_cache = {}

    def gens(f):
        if f not in gens_cache:
            gens_cache[f] = [ref(lat.rep(e)) for e in lat.gens_of(f)]
        return gens_cache[f]

    def elem(K, F):
        e = int(np.nonzero(lat.nxt[K] == F)[0][0])
        return ref(lat.rep(e))

    for i, v in sorted(yex.items()):
        if v == 0:
            continue
        if i < nm:
            a, K = (int(t) for t in L['mono_tag'][i])
            out_rows.append(dict(type='mono', K=gens(K), i=elem(K, a), mult=fr(-v)))
        elif i < nm + ns:
            a, b, J, K = (int(t) for t in L['sub_tag'][i - nm])
            out_rows.append(dict(type='sub', K=gens(K), i=elem(K, a), j=elem(K, b), mult=fr(-v)))
        elif i < L['ci_start'] + L['nci']:
            out_rows.append(dict(type='ci', step=int(i - L['ci_start']), mult=fr(-v)))
        elif L['bstart'] <= i:
            s = cfg.R[i - L['bstart']]
            lam[f"{s[0]},{s[1]}"] = fr(v)
        elif extra_defs is not None and L['xstart'] <= i < L['xstart'] + L['nx']:
            kind, sv, a, b, c, d = extra_defs[i - L['xstart']]
            out_rows.append(dict(type=kind, s=int(sv), a=gens(a), b=gens(b), c=gens(c), d=gens(d),
                                 mult=fr(-v)))
        else:
            raise RuntimeError("extra rows not supported in certificates yet")
    eqlaw = [dict(step=int(t), gens=[ref(g) for g in gF]) for (F, G, t, gF) in L['eqp']]
    steps = []
    for (U, V, nid), kind in zip(cfg.steps, cfg.kinds):
        if kind is None:
            steps.append(dict(U=[int(u) for u in U], V=[ref(g) for g in V]))
        else:
            lk = kind['link']
            steps.append(dict(link=[[int(u) for u in U], int(kind['u']), int(kind['w']),
                                    'id' if lk == 'id' else [int(lk[0]), int(lk[1])]]))
    J = dict(slopes=[list(s) for s in cfg.R], steps=steps,
             extra=[list(map(int, f)) for f in lat.extra_amb], eqlaw=eqlaw, rows=out_rows)
    J['lambda'] = lam
    tot = sum(Fraction(x) for x in lam.values())
    J['claimed_C'] = fr(tot)
    return J, tot


def certify_fast(cfg, lat, L, S, path, verbose=True, extra_defs=None):
    yex = exact_dual(L, S, verbose=verbose)
    bad = check_signs(L, yex)
    if bad:
        raise RuntimeError(f"{len(bad)} wrong-sign multipliers, e.g. {bad[:3]}")
    J, tot = to_json(cfg, lat, L, yex, extra_defs=extra_defs)
    with open(path, 'w') as f:
        json.dump(J, f)
    if verbose:
        print(f"  certificate: C = {tot} = {float(tot):.10f}, {len(J['rows'])} rows -> {path}", flush=True)
    return tot, J
