"""Test all k-subsets of candidate forms (65 {+-1} forms on <= 3 of the 5 free coordinates) on the KT 11/6
gluing; write one JSON line per subset with LP value < 11/6 - 1e-7 (IPM), one line per subset whose LP fails,
plus a final summary that counts both (exit status 1 if any LP failed).
usage: python ksel.py K WORKERS OUT.jsonl [pool=all|mech|min17]"""
import sys, json, time, itertools
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import multiprocessing as mp
from kt import kt116
from extra import extra_forms
G = {}


def lpval(forms):
    from eng import Lattice
    from fastlp import build_lp, solve_lp
    cfg = kt116()
    lat = Lattice(cfg, verbose=False, extra_amb=forms)
    L = build_lp(cfg, lat)
    S = solve_lp(L, opts={'solver': 'simplex'})
    return S['value']


def test(sub):
    try:
        return (lpval([G['c'][i] for i in sub]), sub, None)
    except Exception as e:  # reported and counted, never read as a value
        return (None, sub, repr(e))


def init(c):
    G['c'] = c


if __name__ == '__main__':
    k, workers, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    cfg = kt116()
    c = extra_forms(cfg, (-1, 1), 3)
    subs = list(itertools.combinations(range(len(c)), k))
    print(len(c), 'candidates', len(subs), 'subsets', flush=True)
    t0 = time.time()
    thr = 11 / 6 - 1e-9
    nbelow = nfail = 0
    with open(out, 'w') as fo, mp.Pool(workers, initializer=init, initargs=(c,)) as pool:
        for n, (v, sub, err) in enumerate(pool.imap_unordered(test, subs, chunksize=16)):
            if v is None:
                nfail += 1
                fo.write(json.dumps(dict(error=err, sub=list(sub))) + '\n')
                fo.flush()
            elif v < thr:
                nbelow += 1
                fo.write(json.dumps(dict(v=v, sub=list(sub), forms=[c[i] for i in sub])) + '\n')
                fo.flush()
            if n % 2000 == 0:
                print(f'{n}/{len(subs)} done, {nbelow} below, {nfail} LP failures, {time.time()-t0:.0f}s', flush=True)
    print(f'DONE {len(subs)} subsets, {nbelow} below 11/6, {nfail} LP failures, {time.time()-t0:.0f}s', flush=True)
    if nfail:
        sys.exit(1)
