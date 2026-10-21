"""Parallel evaluation of schemes.  Input: JSON lines {"id":..., "R":3|4, "steps":[[U,[[v,[a,b]],...]],...]}.
Output: JSON lines with value (IPM screening; simplex re-solve if below threshold)."""
import sys, os, json, time, argparse
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import multiprocessing as mp

X, Y, S, T, D = (1, 0), (0, 1), (1, 1), (1, 2), (1, -1)
RS = {3: [X, Y, S], 4: [X, Y, S, T]}
THR = {3: 11 / 6, 4: 7 / 4}


def build(R, steps):
    from eng import Config
    cfg = Config(R)
    for st in steps:
        if isinstance(st, dict):
            U, u, w, link = st['link']
            cfg.attach_link(list(U), u, w, 'id' if link == 'id' else tuple(link))
        else:
            U, V = st
            cfg.attach(list(U), [(v, tuple(s)) for v, s in V])
    return cfg


def eval_one(job):
    from eng import Lattice
    from fastlp import build_lp, solve_lp
    t0 = time.time()
    out = dict(id=job.get('id'), R=job['R'], steps=job['steps'])
    try:
        R = RS[job['R']]
        cfg = build(R, job['steps'])
        lat = Lattice(cfg, verbose=False, max_flats=job.get('max_flats', 60000))
        out['nf'] = lat.nflats
        out['n'] = cfg.n
        L = build_lp(cfg, lat)
        S = solve_lp(L, opts={'solver': 'ipm', 'run_crossover': 'off'})
        v = S['value']
        if v < THR[job['R']] - 1e-6:
            S2 = solve_lp(L)
            out['v_simplex'] = S2['value']
            out['lam'] = [float(x) for x in S2['lam']]
        out['v'] = v
        out['status'] = S['status']
    except Exception as e:
        out['err'] = repr(e)[:200]
    out['t'] = round(time.time() - t0, 3)
    return out


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('inp')
    ap.add_argument('out')
    ap.add_argument('--workers', type=int, default=16)
    a = ap.parse_args()
    jobs = [json.loads(l) for l in open(a.inp)]
    done = set()
    if os.path.exists(a.out):
        for l in open(a.out):
            try:
                done.add(json.loads(l)['id'])
            except Exception:
                pass
    jobs = [j for j in jobs if j.get('id') not in done]
    t0 = time.time()
    n = 0
    with mp.Pool(a.workers, maxtasksperchild=200) as pool, open(a.out, 'a') as f:
        for r in pool.imap_unordered(eval_one, jobs, chunksize=1):
            f.write(json.dumps(r) + "\n")
            f.flush()
            n += 1
    print(f"evaluated {n} in {time.time()-t0:.1f}s")
