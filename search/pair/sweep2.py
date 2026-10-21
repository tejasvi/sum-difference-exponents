"""Parallel sweep of two-set LP configurations (eng2), Shannon only, optionally certified (cert3).
Job (JSON line): {"id": str, "nD": 2|3, "W": [[i,j],...], "ex": [spec,...], "M": 12, "cert": bool, "max_flats": int}
Extras specs: "base34" = 3,4-term +-1 combos of D coordinates; "base3" = 3-term; "W2" = W + a +- b (a, b D coords);
"W3" = W + a +- b +- c; "all3" = all 3-term +-1 combos of all coordinates; "WW" = W_1 +- W_2 + a.
Output: JSON lines with the LP value (IPM) and, if cert and value < thr, the certified lambda."""
import sys, os, json, time, itertools, argparse
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))


def build(job):
    if 'steps' in job:                 # configurations with conditional copies
        import condjob
        return condjob.build(job)
    from eng2 import Config2, F
    c = Config2()
    c.fresh('D')
    for k in range(job.get('nD', 2) - 1):
        c.copy([0, 1], [])
    ws = []
    for wij in job.get('W', []):
        v = c.fresh('W', tuple(wij), wsupport=job.get('wsupport', False))
        ws.append(c.vatoms[v][0])
    for t in job.get('V', []):          # extra vertices: 'UX', 'UY', 'S'
        c.fresh(t)
    dcoords = list(range(2 * job.get('nD', 2)))
    ex = []

    def combos(coords, nz, lead=None):
        out = []
        for S in itertools.combinations(coords, nz):
            for cs in itertools.product((1, -1), repeat=nz):
                if cs[0] < 0:
                    continue
                d = dict(zip(S, cs))
                if lead is not None:
                    d = dict(d)
                    d[lead] = 1
                out.append(F(c, d))
        return out
    allws = list(ws)
    for spec in job.get('ex', []):
        # per-W restriction: 'W3@1' applies spec W3 to the W with index 1 only
        if '@' in spec:
            spec, k = spec.split('@')
            ws = [allws[int(k)]]
        else:
            ws = allws
        if spec == 'base34':
            ex += combos(dcoords, 3) + combos(dcoords, 4)
        elif spec == 'base3':
            ex += combos(dcoords, 3)
        elif spec == 'base4':
            ex += combos(dcoords, 4)
        elif spec == 'W2':
            for w in ws:
                ex += combos(dcoords, 2, lead=w)
        elif spec == 'W3':
            for w in ws:
                ex += combos(dcoords, 3, lead=w)
        elif spec == 'W4':
            for w in ws:
                ex += combos(dcoords, 4, lead=w)
        elif spec in ('W2f', 'W3f', 'W4f'):   # W + (all sign patterns on k D coordinates)
            k = int(spec[1])
            for w in ws:
                for S in itertools.combinations(dcoords, k):
                    for cs in itertools.product((1, -1), repeat=k):
                        d = dict(zip(S, cs))
                        d[w] = 1
                        ex.append(F(c, d))
        elif spec == 'C2':           # a +- 2b over D coordinates
            for a in dcoords:
                for b in dcoords:
                    if a != b:
                        for sb in (2, -2):
                            ex.append(F(c, {a: 1, b: sb}))
        elif spec == 'WC2':          # W +- 2a, 2W +- a
            for w in ws:
                for a in dcoords:
                    for sa in (2, -2):
                        ex.append(F(c, {w: 1, a: sa}))
                    for sa in (1, -1):
                        ex.append(F(c, {w: 2, a: sa}))
        elif spec == 'W1m':          # W - a (differences with W)
            for w in ws:
                for a in dcoords:
                    ex.append(F(c, {w: 1, a: -1}))
        elif spec == '2W2':          # 2W + a +- b
            for w in ws:
                for S in itertools.combinations(dcoords, 2):
                    for sb in (1, -1):
                        ex.append(F(c, {w: 2, S[0]: 1, S[1]: sb}))
        elif spec == 'all3':
            ex += combos(list(range(c.N)), 3)
        elif spec == 'WW':
            for w1, w2 in itertools.combinations(ws, 2):
                for a in dcoords:
                    for s2 in (1, -1):
                        for sa in (1, -1):
                            ex.append(F(c, {w1: 1, w2: s2, a: sa}))
        else:
            raise ValueError(spec)
    nD = job.get('nD', 2)
    if 'forms' in job:
        # explicit forms over names x0,y0,x1,y1,... then w, v, u for the W vertices in order
        import re
        names = []
        for k in range(nD):
            names += [f'x{k}', f'y{k}']
        names += ['w', 'v', 'u', 't'][:len(allws)]
        for sform in job['forms']:
            d = {}
            for sign, var in re.findall(r'([+-]?)([a-z][0-9]*)', sform.replace(' ', '')):
                d[names.index(var)] = d.get(names.index(var), 0) + (-1 if sign == '-' else 1)
            ex.append(F(c, d))
    # automorphisms: permutations of the iid D copies combined with permutations of equal-law W's
    wl = [tuple(w) for w in job.get('W', [])]
    wperms = []
    for perm in itertools.permutations(range(len(allws))):
        if all(wl[i] == wl[perm[i]] for i in range(len(allws))):
            wperms.append(perm)
    autos = []
    for perm in itertools.permutations(range(nD)):
        for wp in wperms:
            if list(perm) == list(range(nD)) and list(wp) == list(range(len(allws))):
                continue
            m = {}
            for k, pk in enumerate(perm):
                m[2 * k] = 2 * pk
                m[2 * k + 1] = 2 * pk + 1
            for i, pi in enumerate(wp):
                m[allws[i]] = allws[pi]
            autos.append(m)
    return c, ex, autos


def run_job(job):
    from eng2 import Lattice2, build_lp2
    from eng643 import solve_lp, IPM
    t0 = time.time()
    out = dict(id=job['id'], job=job)
    try:
        c, ex, autos = build(job)
        lat = Lattice2(c, extra=ex, verbose=False, max_flats=job.get('max_flats', 200000))
        out['flats'] = lat.nflats
        out['d'] = lat.d
        L = build_lp2(c, lat, M=job.get('M', 12), reflect=True, autos=autos)
        out['rows'] = int(L['A'].shape[0])
        S = solve_lp(L, opts=IPM)
        out['v'] = S['value']
        out['status'] = S['status']
        out['t_lp'] = round(time.time() - t0, 1)
        if job.get('cert') and S['value'] < job.get('thr', 1.4480878203):
            import cert4
            path = os.path.join(job.get('certdir', 'certs'), f"{job['id']}.json")
            os.makedirs(job.get('certdir', 'certs'), exist_ok=True)
            lam = cert4.certify(c, lat, job.get('M', 12), [], autos, path)
            if lam is not None:
                out['lam'] = f"{lam.numerator}/{lam.denominator}"
                out['lam_f'] = float(lam)
                out['cert'] = path
    except Exception as e:
        out['err'] = repr(e)[:300]
    out['t'] = round(time.time() - t0, 1)
    return out


if __name__ == '__main__':
    import multiprocessing as mp
    ap = argparse.ArgumentParser()
    ap.add_argument('inp')
    ap.add_argument('out')
    ap.add_argument('--workers', type=int, default=8)
    a = ap.parse_args()
    jobs = [json.loads(l) for l in open(a.inp)]
    done = set()
    if os.path.exists(a.out):
        for l in open(a.out):
            try:
                done.add(json.loads(l)['id'])
            except Exception:
                pass
    jobs = [j for j in jobs if j['id'] not in done]
    with mp.Pool(a.workers, maxtasksperchild=1) as pool, open(a.out, 'a') as f:
        for r in pool.imap_unordered(run_job, jobs, chunksize=1):
            f.write(json.dumps(r) + "\n")
            f.flush()
            print(r['id'], r.get('v'), r.get('lam_f'), r.get('err', ''), r.get('t'), flush=True)
