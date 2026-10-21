"""Cardinality-minimal lattice-row certificates via MILP over a candidate pool.
usage: python milp.py FORMS.json TARGET OUT.json [nrand] [timelimit]"""
import sys, json, time, pickle
from fractions import Fraction
import numpy as np
import scipy.sparse as sp
from scipy.optimize import linprog, milp, LinearConstraint, Bounds
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from latrows import build, lattice_rows, make_L, l1_support, restricted, to_json


def pool_supports(L2, target, nrand, seed=1):
    rng = np.random.default_rng(seed)
    n = L2['ns']
    pool = set()
    for r in range(nrand):
        cost = rng.uniform(0.5, 1.5, n) if r else None
        s = l1_support(L2, target, iters=4, cost=cost, verbose=False)
        pool |= set(int(i) for i in s)
        print(f"  rand {r}: support {len(s)}, pool {len(pool)}", flush=True)
    return sorted(pool)


def card_min(L2, target, cand, timelimit=600):
    A = L2['A'].tocsr()
    n = L2['ns']; nci = L2['nci']; nb = len(L2['bflats'])
    Ac = A[cand].T                        # ncol x p
    Aci = A[n:n + nci].T
    Ab = A[n + nci:].T
    p = len(cand)
    # variables: mu (p), z (p), nu (nci), lam (nb)
    nv = 2 * p + nci + nb
    Aeq = sp.hstack([Ac, sp.csr_matrix((L2['ncol'], p)), Aci, -Ab]).tocsr()
    beq = np.zeros(L2['ncol']); beq[L2['obj_col']] = -1.0
    link = sp.hstack([sp.identity(p), -sp.identity(p), sp.csr_matrix((p, nci + nb))]).tocsr()
    tl = np.zeros((1, nv)); tl[0, 2 * p + nci:] = 1.0
    cons = [LinearConstraint(Aeq, beq, beq), LinearConstraint(link, -np.inf, 0.0),
            LinearConstraint(sp.csr_matrix(tl), -np.inf, float(target))]
    c = np.zeros(nv); c[p:2 * p] = 1.0
    lb = np.concatenate([np.zeros(2 * p), np.full(nci, -np.inf), np.zeros(nb)])
    ub = np.concatenate([np.ones(2 * p), np.full(nci, np.inf), np.full(nb, np.inf)])
    integ = np.concatenate([np.zeros(p), np.ones(p), np.zeros(nci + nb)])
    res = milp(c, constraints=cons, integrality=integ, bounds=Bounds(lb, ub),
               options=dict(time_limit=timelimit, disp=False))
    print(f"  MILP status {res.status} {res.message}; objective {res.fun}", flush=True)
    mu = res.x[:p]
    return [cand[i] for i in range(p) if mu[i] > 1e-9]


if __name__ == '__main__':
    forms = json.load(open(sys.argv[1]))
    target = Fraction(sys.argv[2])
    out = sys.argv[3]
    nrand = int(sys.argv[4]) if len(sys.argv) > 4 else 8
    tlim = float(sys.argv[5]) if len(sys.argv) > 5 else 600
    cfg, lat, L = build(forms)
    Arows, tags = lattice_rows(lat, L)
    L2 = make_L(L, Arows, tags)
    cand = pool_supports(L2, target, nrand)
    supp = card_min(L2, target, cand, tlim)
    S, yex = restricted(L2, np.array(supp))
    J, tot, grouped = to_json(cfg, lat, L, L2, yex)
    json.dump(J, open(out, 'w'))
    pickle.dump(dict(grouped=grouped, masks=lat.masks, E=lat.E, idx=lat.idx, nflats=lat.nflats,
                     extra=lat.extra_amb, eqp=[(F, G, t) for (F, G, t, g) in L['eqp']]),
                open(out.replace('.json', '.pkl'), 'wb'))
    from collections import Counter
    print(f"CERT {out}: C = {tot} = {float(tot):.12f}; grouped rows {len(grouped)} "
          f"{dict(Counter(g['kind'] for g in grouped))}; elemental rows {len(J['rows'])}", flush=True)
