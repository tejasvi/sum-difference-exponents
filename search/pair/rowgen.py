"""Row generation + non-Shannon cut loop + certification on the merged tagged LP (cert4).
The full LP (all elemental Shannon rows) is built once; the solver only sees an active subset:
all non-Shannon rows (bounds, grid, CI, identifications, multigrid, cuts) plus the Shannon rows that were ever
violated or tight.  Dropping valid rows only weakens the LP, so every intermediate value is a valid upper bound
for lambda; at convergence (no violated Shannon row, no new cut) it equals the full LP value.
Usage: python rowgen.py '<job json>' OUTPREFIX [rounds]
env: CUTS=1 (Matus/CC separation), MAXCUTS, MAXQUADS, ADDCAP, RAB, RCD, INIT (initial random Shannon rows)."""
import sys, os, time, json, pickle
import numpy as np
import scipy.sparse as sp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from eng2 import Lattice2
from eng643 import solve_lp, IPM, IPMX
from sweep2 import build
import cert4
from ns2 import separate5b, matus_row, five_row


def main():
    job = json.loads(sys.argv[1])
    prefix = sys.argv[2]
    rounds = int(sys.argv[3]) if len(sys.argv) > 3 else 30
    CUTS = os.environ.get('CUTS', '0') == '1'
    MAXC = int(os.environ.get('MAXCUTS', 600))
    MAXQ = int(os.environ.get('MAXQUADS', 4000))
    ADDCAP = int(os.environ.get('ADDCAP', 1000))
    RAB = int(os.environ.get('RAB', 2))
    RCD = int(os.environ.get('RCD', 1))
    INIT = int(os.environ.get('INIT', 150000))
    VTOL = float(os.environ.get('VTOL', 1e-7))
    STALL = int(os.environ.get('STALL', 4))
    ADDSH = int(os.environ.get('ADDSH', 150000))
    ADDFRAC = float(os.environ.get('ADDFRAC', 0))       # add max(ADDSH, min(ADDFRAC * violated, ADDMAX)) rows
    ADDMAX = int(os.environ.get('ADDMAX', 1500000))
    t0 = time.time()
    c, ex, autos = build(job)
    lat = Lattice2(c, extra=ex, verbose=True, max_flats=job.get('max_flats', 600000))
    M = job.get('M', 12)
    mg = job.get('mg', False)
    infos = []
    if job.get('cuts_pkl'):
        infos = pickle.load(open(job['cuts_pkl'], 'rb'))['infos']
    VEC = os.environ.get('VEC', '1') == '1'
    L = cert4.build_merged_tagged(c, lat, M, infos, autos, mg=mg, rshare=job.get('rshare', False),
                                   rwmap=job.get('rwmap'), vec=VEC, sgrid=job.get('sgrid', 0),
                                   pmerge=job.get('pmerge', False), xshare=job.get('xshare', False))
    assert not (CUTS and job.get('rshare') == 'full'), "cuts not supported with full rshare compression"
    A = L['A'].tocsr()
    nrow = A.shape[0]
    tags = L['tags']
    if isinstance(tags, cert4.LazyTags):
        shannon = np.zeros(nrow, dtype=bool)
        shannon[:tags.n_sh] = True
    else:
        shannon = np.array([t[0] in ('sub', 'mono') for t in tags])
    print(f"full LP {A.shape}, shannon rows {shannon.sum()}, {time.time()-t0:.1f}s", flush=True)
    rng = np.random.default_rng(int(os.environ.get('SEED', 1)))
    KS = tuple(range(1, int(os.environ.get('KMAX', 3)) + 1))
    SS = tuple(range(1, int(os.environ.get('SMAX', 4)) + 1))
    sh_idx = np.nonzero(shannon)[0]
    active = np.zeros(nrow, dtype=bool)
    active[~shannon] = True
    active[rng.choice(sh_idx, size=min(INIT, len(sh_idx)), replace=False)] = True

    def describe(t):
        # lattice-independent description of a Shannon row: (kind, copy, K generator forms, added forms)
        fm = lambda e: tuple(str(x) for x in lat.amb[e])
        if t[0] == 'mono':
            _, cp, a, k = t
            e = int(np.nonzero(lat.nxt[k] == a)[0][0])
            return ('mono', cp, tuple(fm(g) for g in lat.gens_of(k)), (fm(e),))
        _, cp, a, b, j, k = t
        e1 = int(np.nonzero(lat.nxt[k] == a)[0][0])
        e2 = int(np.nonzero(lat.nxt[k] == b)[0][0])
        return ('sub', cp, tuple(fm(g) for g in lat.gens_of(k)), (fm(e1), fm(e2)))
    if os.environ.get('INIT_FROM'):
        # warm start: Shannon rows active at the end of an earlier run (mapped through their generator forms)
        from fractions import Fraction
        descs = pickle.load(open(os.environ['INIT_FROM'], 'rb'))
        if isinstance(tags, cert4.LazyTags):
            # look rows up by the hash of their merged-column signature
            order = np.argsort(L['shash'])
            hs = L['shash'][order]

            class _Pos:
                def __contains__(self, t):
                    return self.get(t) is not None

                def get(self, t):
                    cm = L['cmaps'][t[1]]
                    if t[0] == 'mono':
                        C = np.array([[cm[t[2]], cm[t[3]], -1, -1]]); V = np.array([[1, -1, 0, 0]])
                    else:
                        C = np.array([[cm[t[2]], cm[t[3]], cm[t[4]], cm[t[5]]]]); V = np.array([[1, 1, -1, -1]])
                    C, V = cert4.canon_rows(C, V)
                    h = cert4.row_hash(C, V)[0]
                    p = np.searchsorted(hs, h)
                    return int(order[p]) if p < len(hs) and hs[p] == h else None

                def __getitem__(self, t):
                    return self.get(t)
            tagpos = _Pos()
        else:
            tagpos = {t: i for i, t in enumerate(tags) if t[0] in ('sub', 'mono')}
        hit = 0
        NN = len(lat.amb[0])
        pad = lambda g: [Fraction(x) for x in g] + [Fraction(0)] * (NN - len(g))   # earlier run may have fewer coords
        for kind, cp, Kg, add in descs:
            if any(len(g) > NN for g in Kg + add):
                continue
            es = [lat.form_e(pad(g)) for g in Kg]
            ad = [lat.form_e(pad(g)) for g in add]
            if any(e is None for e in es + ad):
                continue
            k = lat.cl_ids(es) if es else 0
            if kind == 'mono':
                a = int(lat.nxt[k, ad[0]])
                cand = [('mono', cp, a, k)]
            else:
                a, b = int(lat.nxt[k, ad[0]]), int(lat.nxt[k, ad[1]])
                j = lat.cl_ids(es + ad)
                cand = [('sub', cp, a, b, j, k), ('sub', cp, b, a, j, k)]
            for t in cand:
                if t in tagpos:
                    active[tagpos[t]] = True
                    hit += 1
                    break
        del tagpos
        print(f"warm start: {hit} of {len(descs)} rows mapped from {os.environ['INIT_FROM']}", flush=True)
    cutinfos = list(infos)
    cutrows = []           # explicit (flat->w) rows for new cuts, applied to both copies
    seen = set()
    colof, nfc = L['colof'], L['nfc']
    pool_ab = [f for f in range(1, lat.nflats) if lat.rank[f] <= RAB]
    pool_cd = [f for f in range(1, lat.nflats) if lat.rank[f] <= RCD]

    def cut_matrix():
        ri, rj, rv = [], [], []
        k = 0
        for row in cutrows:
            for cp in (0, 1):
                d = {}
                for f, w in row.items():
                    cc = colof[f]
                    if cc >= 0:
                        d[cc + cp * nfc] = d.get(cc + cp * nfc, 0) + w
                for cc, w in d.items():
                    if w:
                        ri.append(k); rj.append(cc); rv.append(w)
                k += 1
        return sp.csr_matrix((rv, (ri, rj)), shape=(k, L['ncol'])), k

    best = None
    hist = []
    for rd in range(rounds):
        X, kx = cut_matrix()
        Asub = A[active]
        L2 = dict(L)
        L2['A'] = sp.vstack([Asub, X]).tocsr() if kx else Asub
        L2['lo'] = np.concatenate([L['lo'][active], np.zeros(kx)])
        L2['hi'] = np.concatenate([L['hi'][active], np.full(kx, np.inf)])
        S = solve_lp(L2, opts=IPM)
        x = S['col_value']
        r = A[shannon] @ x
        viol = np.nonzero(r < -VTOL)[0]
        nviol = len(viol)
        print(f"round {rd}: value {S['value']:.10f} {S['status']} active {active.sum()} cuts {len(cutrows)} "
              f"violated shannon {nviol} ({time.time()-t0:.1f}s)", flush=True)
        added = 0
        if nviol:
            nadd = max(ADDSH, min(int(ADDFRAC * nviol), ADDMAX))
            order = viol[np.argsort(r[viol])][:nadd]
            newrows = sh_idx[order]
            active[newrows] = True
            added += len(newrows)
        if CUTS and (nviol < 1000 or rd % 3 == 2):
            new = []
            for cp in (0, 1):
                H = np.zeros(lat.nflats)
                for f in range(lat.nflats):
                    cc = colof[f]
                    if cc >= 0:
                        H[f] = x[cc + cp * nfc]
                new += separate5b(lat, H, pool_ab, pool_cd, ks=KS, s4=SS, maxcuts=MAXC, maxquads=MAXQ, verbose=False)
            new.sort(key=lambda t: t[0])
            nc = 0
            for v, row, info in new:
                key = tuple(sorted(row.items()))
                if key in seen:
                    continue
                seen.add(key)
                cutrows.append(row)
                cutinfos.append(info)
                nc += 1
                if nc >= ADDCAP:
                    break
            added += nc
            print(f"   new cuts {nc}", flush=True)
            pickle.dump(dict(infos=cutinfos), open(prefix + '_cuts.pkl', 'wb'))
        hist.append(S['value'])
        if not added:
            break
        if len(hist) > STALL and max(hist[-STALL - 1:]) - min(hist[-STALL - 1:]) < 1e-8 and nviol < 2000:
            print("stalled: value unchanged; certifying", flush=True)
            break
    # save the active Shannon rows (lattice independent) for warm starts of related runs
    try:
        pickle.dump([describe(tags[i]) for i in np.nonzero(active & shannon)[0]], open(prefix + '_active.pkl', 'wb'))
    except Exception as ex:
        print('could not save active rows:', ex, flush=True)
    # final: certify on the active Shannon rows + all other rows + cuts (rebuild tagged LP with the cuts)
    print("certifying ...", flush=True)
    if len(cutinfos) == len(infos):
        # no new cuts: certify directly on the active rows of L
        keep = active | ~shannon
        Lk = dict(L)
        Lk['A'] = A[keep]
        Lk['lo'] = L['lo'][keep]
        Lk['hi'] = L['hi'][keep]
        Lk['tags'] = [tags[i] for i in np.nonzero(keep)[0]]
    else:
        Lc = cert4.build_merged_tagged(c, lat, M, cutinfos, autos, mg=mg, rshare=job.get('rshare', False),
                                        rwmap=job.get('rwmap'))
        tags2 = Lc['tags']
        keep = np.array([not (t[0] in ('sub', 'mono')) for t in tags2])
        # map active shannon rows of L to rows of Lc by tag (both built identically for Shannon rows)
        act_tags = set(tags[i] for i in np.nonzero(active & shannon)[0])
        for i, t in enumerate(tags2):
            if t[0] in ('sub', 'mono') and t in act_tags:
                keep[i] = True
        Lk = dict(Lc)
        Lk['A'] = Lc['A'].tocsr()[keep]
        Lk['lo'] = Lc['lo'][keep]
        Lk['hi'] = Lc['hi'][keep]
        Lk['tags'] = [t for t, k in zip(tags2, keep) if k]
    S = solve_lp(Lk, opts=IPMX)
    print(f"final restricted LP {Lk['A'].shape}: value {S['value']:.12f} {S['status']}", flush=True)
    for tol in (1e-9, 1e-8, 1e-10, 1e-7):
        try:
            yex = cert4.exact_dual(Lk, S['row_dual'], tol)
        except RuntimeError as e:
            print('tol', tol, e, flush=True)
            continue
        bad = [rr for rr, v in yex.items() if (Lk['lo'][rr] != Lk['hi'][rr]) and
               ((np.isinf(Lk['hi'][rr]) and v > 0) or (np.isinf(Lk['lo'][rr]) and v < 0))]
        if bad:
            print('tol', tol, 'bad signs', len(bad), flush=True)
            continue
        J, lam, nm = cert4.explicit_certificate(c, lat, Lk, yex, M, autos)
        json.dump(J, open(prefix + '.json', 'w'))
        print(f"certified lambda = {lam} = {float(lam):.12f} -> {prefix}.json ({len(J['rows'])} rows)", flush=True)
        break


if __name__ == '__main__':
    main()
