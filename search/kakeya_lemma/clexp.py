"""Copy-lemma separation rounds on top of a (forms, cuts) state: cuts may be matus / dfz / lem rows.
Each round: solve the LP, take the NQ most Ingleton-violating quadruples of candidate flats (ordered a,b | c,d),
for each quadruple and each of the 4 orientations (a<->b, c<->d) and each copy scheme (DFZ step patterns) solve
the separation LP (clsep.separate); keep the best exact lemma per quadruple-orientation (if violated); add rows.
Also runs Matus + DFZ separation (unless MODE=cl).  python clexp.py NAME FORMS CUTS ROUNDS NQ WORKERS [THREADS]
Writes runs/NAME_cuts.json (defs) and runs/NAME_lemmas.json (lemma registry)."""
import sys, json, time, os
import numpy as np
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import multiprocessing as mp

G = {}


def init(schemes):
    G['schemes'] = schemes


def task(args):
    qi, orient, h4 = args
    import clsep
    best = (0.0, None, None)
    for raw, steps in G['schemes']:
        try:
            v, L = clsep.separate(h4, raw, steps)
        except Exception:
            continue
        if v is not None and L is not None and v < best[0] - 1e-12:
            best = (v, raw, L)
    return qi, orient, best


def main():
    name, formsf, cutsf, rounds, nq, workers = sys.argv[1:7]
    rounds, nq, workers = int(rounds), int(nq), int(workers)
    threads = int(sys.argv[7]) if len(sys.argv) > 7 else 32
    mode = os.environ.get('MODE', 'all')
    from eng import Lattice
    from fastlp import build_lp, solve_lp
    from kt import kt116, kt74
    from nonshannon import matus_terms
    from sepnb import join_partial, PJ, most_violated_alls_p
    from dfzsep import dfz_terms, most_violated_dfz_p, load_dfz
    import clsep
    t0 = time.time()
    cfg = kt74() if os.environ.get('SCHEME') == 'kt74' else kt116()
    lat = Lattice(cfg, verbose=False, extra_amb=json.load(open(formsf)))
    C0 = json.load(open(cutsf))
    defs = [tuple(d) for d in C0['defs']]
    reg = {}
    lemf = cutsf.replace('_cuts.json', '_lemmas.json')
    if os.path.exists(lemf):
        reg.update(json.load(open(lemf)))
    cand = [f for f in range(1, lat.nflats) if lat.rank[f] <= 2]
    allc = sorted(set(cand) | set(x for d in defs for x in d[2:]))
    Jp, col = join_partial(lat, allc)
    J = PJ(Jp, col)
    ks, W = load_dfz()
    Wd = {k: [int(x) for x in W[i]] for i, k in enumerate(ks)}
    keymap = {}
    for lid, L in reg.items():
        keymap[clsep.lemma_key(L)] = lid
    extra, seen, D = [], set(), []

    def row(d):
        kind, s, a, b, c, dd = d
        if kind == 'matus':
            return matus_terms(J, a, b, c, dd, s)
        if kind == 'dfz':
            return dfz_terms(J, a, b, c, dd, Wd[s])
        return clsep.lemma_terms(clsep.quad_flats(J, a, b, c, dd), reg[s]['coef'])

    def add(d):
        dct = row(d)
        key = tuple(sorted(dct.items()))
        if dct and key not in seen:
            seen.add(key); extra.append(dct); D.append(tuple(d))
            return 1
        return 0
    for d in defs:
        add(d)
    schemes = list(clsep.schemes_dfz().items())
    candarr = np.array(cand, dtype=np.int64)
    Wing = np.array([[1, 1, 0, 0, 1, 0, 0, 1, 0]], dtype=np.float64)
    print(f'{name}: flats {lat.nflats}, cand {len(cand)}, {len(D)} rows, {len(schemes)} schemes, mode {mode}'
          f'  [{time.time()-t0:.0f}s]', flush=True)
    pool = mp.Pool(workers, initializer=init, initargs=(schemes,))
    for it in range(rounds + 1):
        L = build_lp(cfg, lat, extra_rows=[(dd, 0.0, np.inf) for dd in extra])
        S = solve_lp(L, opts={'solver': 'ipm', 'run_crossover': 'on'})
        nl = sum(1 for d in D if d[0] == 'lem')
        print(f' round {it}: LP {S["value"]:.10f} {S["status"]} rows {len(D)} (lem {nl}, registry {len(reg)})'
              f'  [{time.time()-t0:.0f}s]', flush=True)
        json.dump(dict(defs=D, value=S['value']), open(f'runs/{name}_cuts.json', 'w'))
        json.dump(reg, open(f'runs/{name}_lemmas.json', 'w'))
        if it == rounds:
            break
        colof = L['colof']
        h = np.where(colof >= 0, S['col_value'][np.maximum(colof, 0)], 0.0)
        newm = newd = 0
        if mode != 'cl':
            vm = most_violated_alls_p(h, Jp, col, candarr, smax=200, top=400, threads=threads)
            newm = sum(add(('matus', s, a, b, c, d)) for (v, s, a, b, c, d) in vm)
            vd = most_violated_dfz_p(h, Jp, col, candarr, W, top=400, threads=threads)
            newd = sum(add(('dfz', ks[k], a, b, c, d)) for (v, k, a, b, c, d) in vd)
        vi = most_violated_dfz_p(h, Jp, col, candarr, Wing, top=nq, threads=threads)
        quads = [(a, b, c, d) for (v, k, a, b, c, d) in vi]
        tasks = []
        for qi, (a, b, c, d) in enumerate(quads):
            for orient, (p, q, r, s) in enumerate([(a, b, c, d), (b, a, c, d), (a, b, d, c), (b, a, d, c)]):
                fl = clsep.quad_flats(J, p, q, r, s)
                tasks.append((qi, orient, [float(h[f]) for f in fl]))
        res = pool.map(task, tasks, chunksize=1)
        newl, vals = 0, []
        for qi, orient, (v, raw, Lm) in res:
            if Lm is None:
                continue
            a, b, c, d = quads[qi]
            p, q, r, s = [(a, b, c, d), (b, a, c, d), (a, b, d, c), (b, a, d, c)][orient]
            k = clsep.lemma_key(Lm)
            if k not in keymap:
                lid = f'cl{len(reg)}'
                reg[lid] = Lm; keymap[k] = lid
            vals.append(v)
            newl += add(('lem', keymap[k], p, q, r, s))
        print(f'   matus new {newm}, dfz new {newd}, copy-lemma: {len(quads)} quads, {len(vals)} violated '
              f'(best {min(vals) if vals else 0:.3e}), new rows {newl}  [{time.time()-t0:.0f}s]', flush=True)
        if newm + newd + newl == 0:
            break
    pool.close()


if __name__ == '__main__':
    main()
