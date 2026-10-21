"""Forward selection of extra forms: start from a base set, test every candidate form, add the best.
python fwdsel.py NAME SCHEME BASEJSON|none CMAX NZMAX ROUNDS WORKERS"""
import sys, json, time, itertools, os
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import multiprocessing as mp
from kt import kt116, kt74
from extra import coord_basis
G = {}

def lpval(forms):
    from eng import Lattice
    from fastlp import build_lp, solve_lp
    cfg = G['fn']()
    lat = Lattice(cfg, verbose=False, extra_amb=forms, max_flats=200000)
    L = build_lp(cfg, lat)
    S = solve_lp(L, opts={'solver': 'ipm', 'run_crossover': 'off'})
    return S['value'], lat.nflats

def test(f):
    try:
        v, nf = lpval(G['cur'] + [f])
        return (v, nf, f)
    except Exception as e:
        return (9.0, -1, f)

def init(fn, cur):
    G['fn'] = fn; G['cur'] = cur

if __name__ == '__main__':
    name, scheme, base, cmax, nzmax, rounds, workers = sys.argv[1:8]
    cmax, nzmax, rounds, workers = int(cmax), int(nzmax), int(rounds), int(workers)
    fn = kt116 if scheme == 'kt116' else kt74
    cfg = fn()
    basis = coord_basis(cfg)
    cur = json.load(open(base)) if base != 'none' else []
    # candidates: all integer combos with |c| <= cmax, nz <= nzmax, first nonzero positive, primitive
    from math import gcd
    cands = []
    seen = set()
    nb = len(basis)
    for nz in range(1, nzmax + 1):
        for S in itertools.combinations(range(nb), nz):
            for cs in itertools.product([c for c in range(-cmax, cmax + 1) if c], repeat=nz):
                if cs[0] < 0: continue
                g = 0
                for c in cs: g = gcd(g, abs(c))
                if g != 1: continue
                f = [0] * (2 * cfg.n)
                for i, c in zip(S, cs):
                    f = [a + c * b for a, b in zip(f, basis[i])]
                t = tuple(f)
                if t not in seen:
                    seen.add(t); cands.append(f)
    names = ['x%d' % (i // 2) if i % 2 == 0 else 'y%d' % (i // 2) for i in range(2 * cfg.n)]
    nm = lambda f: ' '.join(('%+d' % c) + names[i] for i, c in enumerate(f) if c)
    init(fn, cur)
    v0, nf0 = lpval(cur)
    print(f'{name}: base {len(cur)} forms value {v0:.9f} flats {nf0}; {len(cands)} candidates', flush=True)
    for r in range(rounds):
        t0 = time.time()
        pool_c = [f for f in cands if f not in cur]
        with mp.Pool(workers, initializer=init, initargs=(fn, cur)) as pool:
            res = pool.map(test, pool_c, chunksize=4)
        res.sort(key=lambda z: z[0])
        best = res[0]
        print(f' round {r}: best {best[0]:.9f} via {nm(best[2])} (flats {best[1]});  next: ' +
              ', '.join(f'{z[0]:.6f} {nm(z[2])}' for z in res[1:6]) + f'  [{time.time()-t0:.0f}s]', flush=True)
        if best[0] >= v0 - 1e-8:
            print(' no improvement; stop', flush=True); break
        cur = cur + [best[2]]; v0 = best[0]
        json.dump(cur, open(f'runs/{name}_forms.json', 'w'))
    print('final', v0, len(cur), flush=True)
