"""Greedy forward selection of extra forms UNDER Matus cuts, for the KT 11/6 configuration.
Each round: for every candidate form f, build the lattice of (base forms + f), transfer the current cuts (via
generators), solve the LP (crossover) and record the value; add the best form, then run separation rounds on the
new lattice (all s, rank<=2 candidates) to refresh the cut set.
python fwdmatus.py NAME BASE_FORMS BASE_CUTS ROUNDS WORKERS [CMAX] [NZMAX]"""
import sys, json, time, itertools, os
import numpy as np
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import multiprocessing as mp
from math import gcd

G = {}


def mkcfg():
    from kt import kt116, kt74
    return kt74() if os.environ.get('SCHEME') == 'kt74' else kt116()


def lattice_for(forms):
    from eng import Lattice
    cfg = mkcfg()
    return cfg, Lattice(cfg, verbose=False, extra_amb=forms)


def tr_cuts(latS, cfg, lat, defs):
    """Map cut flats of latS into lat (same configuration) via generator forms."""
    key2e = {tuple(e): i for i, e in enumerate(lat.E)}
    def tr(f):
        return lat.cl_ids([key2e[tuple(latS.E[e])] for e in latS.gens_of(f)])
    return [(s, tr(a), tr(b), tr(c), tr(d)) for (kind, s, a, b, c, d) in defs]


def lp_with_cuts(cfg, lat, cuts):
    from fastlp import build_lp, solve_lp
    from nonshannon import matus_terms
    from sepnb import join_partial, PJ
    flats = sorted(set(x for c in cuts for x in c[1:]))
    Jp, col = join_partial(lat, flats)
    J = PJ(Jp, col)
    extra, defs, seen = [], [], set()
    for (s, a, b, c, d) in cuts:
        dct = matus_terms(J, a, b, c, d, s)
        key = tuple(sorted(dct.items()))
        if dct and key not in seen:
            seen.add(key); extra.append(dct); defs.append(('matus', s, a, b, c, d))
    L = build_lp(cfg, lat, extra_rows=[(dd, 0.0, np.inf) for dd in extra])
    S = solve_lp(L, opts={'solver': 'ipm', 'run_crossover': 'on'})
    return S, L, defs, extra


def eval_candidate(f):
    try:
        forms = G['base'] + [f]
        cfg, lat = lattice_for(forms)
        cuts = tr_cuts(G['latS'], cfg, lat, G['defs'])
        S, L, defs, extra = lp_with_cuts(cfg, lat, cuts)
        return (S['value'], f, lat.nflats)
    except Exception as e:
        return (9.0, f, -1)


def init(base, defs):
    from eng import Lattice
    G['base'] = base
    G['defs'] = defs
    cfg = mkcfg()
    G['latS'] = Lattice(cfg, verbose=False, extra_amb=base)


def separate(cfg, lat, defs, rounds, threads=16):
    from nonshannon import matus_terms
    from sepnb import join_partial, PJ, most_violated_alls_p
    from fastlp import build_lp, solve_lp
    cand = [f for f in range(1, lat.nflats) if lat.rank[f] <= 2]
    cutflats = set(x for d in defs for x in d[2:])
    allc = sorted(set(cand) | cutflats)
    Jp, col = join_partial(lat, allc)
    J = PJ(Jp, col)
    extra, seen = [], set()
    for d in defs:
        dct = matus_terms(J, d[2], d[3], d[4], d[5], d[1])
        extra.append(dct); seen.add(tuple(sorted(dct.items())))
    candarr = np.array(cand, dtype=np.int64)
    S = None
    for it in range(rounds):
        L = build_lp(cfg, lat, extra_rows=[(dd, 0.0, np.inf) for dd in extra])
        S = solve_lp(L, opts={'solver': 'ipm', 'run_crossover': 'on'})
        colof = L['colof']
        h = np.where(colof >= 0, S['col_value'][np.maximum(colof, 0)], 0.0)
        viol = most_violated_alls_p(h, Jp, col, candarr, smax=200, top=400, threads=threads)
        new = 0
        for (v, s, a, b, c, d) in viol:
            dct = matus_terms(J, a, b, c, d, s)
            key = tuple(sorted(dct.items()))
            if dct and key not in seen:
                seen.add(key); extra.append(dct); defs.append(('matus', s, a, b, c, d)); new += 1
        print(f'    sep round {it}: LP {S["value"]:.10f} cuts {len(extra)} new {new}', flush=True)
        if new == 0:
            break
    return defs, S


if __name__ == '__main__':
    name, basef, cutsf, rounds, workers = sys.argv[1:6]
    rounds, workers = int(rounds), int(workers)
    cmax = int(sys.argv[6]) if len(sys.argv) > 6 else 1
    nzmax = int(sys.argv[7]) if len(sys.argv) > 7 else 5
    from extra import coord_basis
    base = json.load(open(basef))
    defs = [tuple(d) for d in json.load(open(cutsf))['defs']]
    cfg0 = mkcfg()
    basis = coord_basis(cfg0)
    cands, seenf = [], set(tuple(f) for f in base)
    for nz in range(1, nzmax + 1):
        for S_ in itertools.combinations(range(len(basis)), nz):
            for cs in itertools.product([c for c in range(-cmax, cmax + 1) if c], repeat=nz):
                if cs[0] < 0:
                    continue
                g = 0
                for c in cs:
                    g = gcd(g, abs(c))
                if g != 1:
                    continue
                f = [0] * (2 * cfg0.n)
                for i, c in zip(S_, cs):
                    f = [a + c * b for a, b in zip(f, basis[i])]
                if tuple(f) not in seenf and tuple(-x for x in f) not in seenf:
                    seenf.add(tuple(f)); cands.append(f)
    print(f'{name}: base {len(base)} forms, {len(defs)} cuts, {len(cands)} candidate forms', flush=True)
    t0 = time.time()
    for r in range(rounds):
        with mp.Pool(workers, initializer=init, initargs=(base, defs)) as pool:
            res = pool.map(eval_candidate, cands, chunksize=1)
        res.sort(key=lambda z: z[0])
        best = res[0]
        print(f' round {r}: best {best[0]:.10f} via {best[1]} (flats {best[2]}); next '
              f'{[round(z[0], 9) for z in res[1:6]]}  [{time.time()-t0:.0f}s]', flush=True)
        if best[0] > 8:
            break
        # adopt the best form, refresh cuts by separation on the new lattice
        cfgS, latS = lattice_for(base)
        base = base + [best[1]]
        cands = [f for f in cands if f != best[1]]
        cfg, lat = lattice_for(base)
        cuts = tr_cuts(latS, cfg, lat, defs)
        defs = [('matus', s, a, b, c, d) for (s, a, b, c, d) in cuts]
        defs, S = separate(cfg, lat, defs, rounds=4)
        json.dump(base, open(f'runs/{name}_forms.json', 'w'))
        json.dump(dict(defs=defs, value=S['value'] if S else None), open(f'runs/{name}_cuts.json', 'w'))
        print(f'  adopted; {len(base)} forms, {len(defs)} cuts, LP {S["value"] if S else None}  [{time.time()-t0:.0f}s]',
              flush=True)
