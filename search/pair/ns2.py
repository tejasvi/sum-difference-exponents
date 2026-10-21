"""Non-Shannon cutting planes (Matus four-variable family) for eng2 LPs.
M_s(a,b,c,d) = I(b;c|a) + s*[abcd] + C(s+1,2)*(I(a;c|b) + I(a;b|c)) >= 0  (Matus 2007),
[abcd] = -I(a;b) + I(a;b|c) + I(a;b|d) + I(c;d).  s = 1 is a form of Zhang-Yeung.
Variables are flats (closed sets of forms); joints are closures of unions.  Only Ingleton-violating
quadruples can violate M_s, so we search those first (vectorized)."""
import sys, time, itertools
import numpy as np
import scipy.sparse as sp
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from eng643 import solve_lp, IPM, IPMX


def join_table(lat, pool):
    """T[f, k] = flat id of cl(f u pool[k]) for every flat f."""
    nf = lat.nflats
    T = np.zeros((nf, len(pool)), dtype=np.int64)
    gens = [lat.gens_of(g) for g in pool]
    for k, gs in enumerate(gens):
        cur = np.arange(nf)
        for e in gs:
            cur = lat.nxt[cur, e]
        T[:, k] = cur
    return T


def matus_row(s, a, b, c, d, J):
    T = {}

    def add(f, w):
        if f != 0:
            T[f] = T.get(f, 0) + w

    def addI(w, x, y, z=None):
        if z is None:
            add(x, w); add(y, w); add(J(x, y), -w)
        else:
            add(J(x, z), w); add(J(y, z), w); add(J(x, y, z), -w); add(z, -w)
    addI(1, b, c, a)
    addI(-s, a, b)
    addI(s, a, b, c)
    addI(s, a, b, d)
    addI(s, c, d)
    k = s * (s + 1) // 2
    addI(k, a, c, b)
    addI(k, a, b, c)
    return {f: w for f, w in T.items() if w != 0}


def separate(lat, H, pool, svals=(1, 2, 3, 4), tol=1e-7, maxcuts=500, verbose=True):
    """H: entropy per flat (array).  Returns list of (violation, row dict)."""
    t0 = time.time()
    P = len(pool)
    pidx = {f: k for k, f in enumerate(pool)}
    T = join_table(lat, pool)
    Hp = H[np.array(pool)]
    Hcd = H[T[np.array(pool)]]          # P x P : H(c u d)
    cache = {}

    def J(*fs):
        key = tuple(sorted(set(fs)))
        if key not in cache:
            es = []
            for f in key:
                es += lat.gens_of(f)
            cache[key] = lat.cl_ids(es)
        return cache[key]
    cands = []
    for ia in range(P):
        a = pool[ia]
        for ib in range(ia + 1, P):
            b = pool[ib]
            ab = T[a, ib]
            if ab == a or ab == b:
                continue      # I(a;b) structure degenerate (one contains the other)
            const = -H[a] - H[b] + H[ab]
            u = H[T[a]] + H[T[b]] - H[T[ab]]          # over c (pool index)
            M = const + u[:, None] + u[None, :] - Hcd
            M[ia, :] = 1; M[:, ia] = 1; M[ib, :] = 1; M[:, ib] = 1
            np.fill_diagonal(M, 1)
            idx = np.argwhere(M < -tol)
            for ic, id_ in idx:
                if ic < id_:
                    cands.append((M[ic, id_], a, b, pool[ic], pool[id_]))
    if verbose:
        print(f"  Ingleton-violating quadruples: {len(cands)} ({time.time()-t0:.1f}s)", flush=True)
    cands.sort()
    out = []
    seen = set()
    for ing, a, b, c, d in cands[:20000]:
        for (x, y) in ((a, b), (b, a)):
            for (z, w) in ((c, d), (d, c)):
                for s in svals:
                    row = matus_row(s, x, y, z, w, J)
                    val = sum(wt * H[f] for f, wt in row.items())
                    if val < -tol:
                        key = tuple(sorted(row.items()))
                        if key not in seen:
                            seen.add(key)
                            out.append((val, row, (s, x, y, z, w)))
    out.sort(key=lambda t: t[0])
    if verbose:
        print(f"  violated Matus rows: {len(out)}, worst {out[0][0] if out else None} ({time.time()-t0:.1f}s)",
              flush=True)
    return out[:maxcuts]


def cut_loop2(L, lat, pool, rounds=10, per_round=200, svals=(1, 2, 3, 4), ncopies=1, verbose=True, opts=IPMX):
    A0, lo0, hi0 = L['A'], L['lo'], L['hi']
    colof = L['colof']
    nfc = L['nflatcol']
    cuts = []
    hist = []
    S = None
    for rd in range(rounds):
        L2 = dict(L)
        if cuts:
            ri, rj, rv = [], [], []
            k = 0
            for row in cuts:
                for cp in range(ncopies):
                    d = {}
                    for f, w in row.items():
                        c = colof[f]
                        if c >= 0:
                            d[c + cp * nfc] = d.get(c + cp * nfc, 0) + w
                    for c, w in d.items():
                        if w:
                            ri.append(k); rj.append(c); rv.append(w)
                    k += 1
            X = sp.csr_matrix((rv, (ri, rj)), shape=(k, L['ncol']))
            L2['A'] = sp.vstack([A0, X]).tocsr()
            L2['lo'] = np.concatenate([lo0, np.zeros(k)])
            L2['hi'] = np.concatenate([hi0, np.full(k, np.inf)])
        S = solve_lp(L2, opts=opts)
        hist.append(S['value'])
        if verbose:
            print(f" round {rd}: value {S['value']:.9f} ({S['status']}), cuts {len(cuts)}", flush=True)
        H = np.zeros(lat.nflats)
        cv = S['col_value']
        for f in range(lat.nflats):
            c = colof[f]
            if c >= 0:
                H[f] = cv[c]
        new = separate(lat, H, pool, svals=svals, maxcuts=per_round, verbose=verbose)
        if not new:
            break
        cuts += [row for v, row, info in new]
    return hist, cuts, S


# ---------------------------------------------------------------------------------------------
# five-variable families (Kleinwaks' Thm 3.4/3.5 = Csirmaz-Csirmaz Thm 22 and (31)), with Ingleton [abcd] or [acbd]:
#   M_k = I(b;z|a) + k(Ing + I(a;z|b) + I(a;b|z)) + C(k,2)(I(a;c|b) + I(a;b|c))
#   C_k = I(a;b|z) + k(Ing + I(a;z|b) + I(b;z|a)) + C(k,2)(I(a;c|b) + I(b;c|a))

def ingleton_terms(x, y, z, w, J):
    """[x y z w] = -I(x;y) + I(x;y|z) + I(x;y|w) + I(z;w) as dict."""
    T = {}

    def add(f, wt):
        if f != 0:
            T[f] = T.get(f, 0) + wt

    def addI(wt, p, q, r=None):
        if r is None:
            add(p, wt); add(q, wt); add(J(p, q), -wt)
        else:
            add(J(p, r), wt); add(J(q, r), wt); add(J(p, q, r), -wt); add(r, -wt)
    addI(-1, x, y); addI(1, x, y, z); addI(1, x, y, w); addI(1, z, w)
    return T


def five_row(fam, k, a, b, c, d, z, variant, J):
    T = {}

    def add(f, wt):
        if f != 0:
            T[f] = T.get(f, 0) + wt

    def addI(wt, p, q, r=None):
        if r is None:
            add(p, wt); add(q, wt); add(J(p, q), -wt)
        else:
            add(J(p, r), wt); add(J(q, r), wt); add(J(p, q, r), -wt); add(r, -wt)
    ing = ingleton_terms(a, b, c, d, J) if variant == 'abcd' else ingleton_terms(a, c, b, d, J)
    for f, wt in ing.items():
        add(f, k * wt)
    kk = k * (k - 1) // 2
    if fam == 'M':
        addI(1, b, z, a); addI(k, a, z, b); addI(k, a, b, z)
        addI(kk, a, c, b); addI(kk, a, b, c)
    else:
        addI(1, a, b, z); addI(k, a, z, b); addI(k, b, z, a)
        addI(kk, a, c, b); addI(kk, b, c, a)
    return {f: wt for f, wt in T.items() if wt != 0}


def separate5(lat, H, pool, ks=(1, 2, 3), s4=(1, 2, 3, 4), tol=1e-7, maxcuts=500, maxquads=4000, verbose=True):
    t0 = time.time()
    P = len(pool)
    parr = np.array(pool)
    T = join_table(lat, pool)
    Hp = H[parr]
    Hcd = H[T[parr]]
    cache = {}

    def J(*fs):
        key = tuple(sorted(set(fs)))
        if key not in cache:
            es = []
            for f in key:
                es += lat.gens_of(f)
            cache[key] = lat.cl_ids(es)
        return cache[key]
    cands = []
    for ia in range(P):
        a = pool[ia]
        for ib in range(ia + 1, P):
            b = pool[ib]
            ab = T[a, ib]
            if ab == a or ab == b:
                continue
            const = -H[a] - H[b] + H[ab]
            u = H[T[a]] + H[T[b]] - H[T[ab]]
            M = const + u[:, None] + u[None, :] - Hcd
            M[ia, :] = 1; M[:, ia] = 1; M[ib, :] = 1; M[:, ib] = 1
            np.fill_diagonal(M, 1)
            for ic, id_ in np.argwhere(M < -tol):
                if ic < id_:
                    cands.append((M[ic, id_], a, b, pool[ic], pool[id_]))
    cands.sort()
    cands = cands[:maxquads]
    if verbose:
        print(f"  Ingleton-violating quadruples used: {len(cands)} ({time.time()-t0:.1f}s)", flush=True)
    out, seen = [], set()

    def consider(row, info):
        val = sum(wt * H[f] for f, wt in row.items())
        if val < -tol:
            key = tuple(sorted(row.items()))
            if key not in seen:
                seen.add(key)
                out.append((val, row, info))

    def Hj(*fs):
        return H[J(*fs)]
    for ing, x, y, zz, ww in cands:
        # roles: [abcd] with (a,b) from (x,y), (c,d) from (zz,ww); [acbd] with (a,c) from (x,y), (b,d) from (zz,ww)
        roles = []
        for (p1, p2) in ((x, y), (y, x)):
            for (q1, q2) in ((zz, ww), (ww, zz)):
                roles.append(('abcd', p1, p2, q1, q2))          # a,b,c,d
                roles.append(('acbd', p1, q1, p2, q2))          # a,b,c,d with Ingleton [a c b d] violated
        for (variant, a, b, c, d) in roles:
            if variant == 'abcd':
                for s in s4:
                    consider(matus_row(s, a, b, c, d, J), ('M4', s, a, b, c, d))
            ia_ = np.searchsorted(parr, a) if False else None
            # vectorized over z in pool
            ab = J(a, b)
            ing_val = sum(wt * H[f] for f, wt in (ingleton_terms(a, b, c, d, J) if variant == 'abcd'
                                                   else ingleton_terms(a, c, b, d, J)).items())
            Iacb = Hj(a, b) + Hj(c, b) - Hj(a, b, c) - H[b]
            Iabc = Hj(a, c) + Hj(b, c) - Hj(a, b, c) - H[c]
            Ibca = Hj(b, a) + Hj(c, a) - Hj(a, b, c) - H[a]
            Haz = H[T[a]]; Hbz = H[T[b]]; Habz = H[T[ab]]
            Ibz_a = H[ab] + Haz - Habz - H[a]
            Iaz_b = H[ab] + Hbz - Habz - H[b]
            Iab_z = Haz + Hbz - Habz - Hp
            for k in ks:
                kk = k * (k - 1) // 2
                vM = Ibz_a + k * (ing_val + Iaz_b + Iab_z) + kk * (Iacb + Iabc)
                vC = Iab_z + k * (ing_val + Iaz_b + Ibz_a) + kk * (Iacb + Ibca)
                for fam, vec in (('M', vM), ('C', vC)):
                    for iz in np.nonzero(vec < -tol)[0][:5]:
                        z = pool[iz]
                        consider(five_row(fam, k, a, b, c, d, z, variant, J), (fam, k, variant, a, b, c, d, z))
    out.sort(key=lambda t: t[0])
    if verbose:
        print(f"  violated rows: {len(out)}, worst {out[0][0] if out else None} ({time.time()-t0:.1f}s)", flush=True)
    return out[:maxcuts]


def cut_loop5(L, lat, pool, rounds=10, per_round=300, ncopies=1, verbose=True, opts=IPMX, **kw):
    A0, lo0, hi0 = L['A'], L['lo'], L['hi']
    colof = L['colof']
    nfc = L['nflatcol']
    cuts, hist, infos = [], [], []
    S = None
    for rd in range(rounds):
        L2 = dict(L)
        if cuts:
            ri, rj, rv = [], [], []
            k = 0
            for row in cuts:
                for cp in range(ncopies):
                    d = {}
                    for f, w in row.items():
                        c = colof[f]
                        if c >= 0:
                            d[c + cp * nfc] = d.get(c + cp * nfc, 0) + w
                    for c, w in d.items():
                        if w:
                            ri.append(k); rj.append(c); rv.append(w)
                    k += 1
            X = sp.csr_matrix((rv, (ri, rj)), shape=(k, L['ncol']))
            L2['A'] = sp.vstack([A0, X]).tocsr()
            L2['lo'] = np.concatenate([lo0, np.zeros(k)])
            L2['hi'] = np.concatenate([hi0, np.full(k, np.inf)])
        S = solve_lp(L2, opts=opts)
        hist.append(S['value'])
        if verbose:
            print(f" round {rd}: value {S['value']:.9f} ({S['status']}), cuts {len(cuts)}", flush=True)
        new = []
        cv = S['col_value']
        for cp in range(ncopies):
            H = np.zeros(lat.nflats)
            for f in range(lat.nflats):
                c = colof[f]
                if c >= 0:
                    H[f] = cv[c + cp * nfc]
            new += separate5(lat, H, pool, maxcuts=per_round, verbose=verbose, **kw)
        if not new:
            break
        new.sort(key=lambda t: t[0])
        seenk = set(tuple(sorted(r.items())) for r in cuts)
        for v, row, info in new[:per_round * ncopies]:
            kk = tuple(sorted(row.items()))
            if kk not in seenk:
                seenk.add(kk)
                cuts.append(row)
                infos.append(info)
    return hist, cuts, infos, S


def separate5b(lat, H, pool_ab, pool_cd, ks=(1, 2, 3), s4=(1, 2, 3, 4), tol=1e-7, maxcuts=500, maxquads=4000,
               verbose=True):
    """As separate5, but (a, b) range over pool_ab, (c, d) over pool_cd, z over pool_cd."""
    t0 = time.time()
    Pc = len(pool_cd)
    carr = np.array(pool_cd)
    Tc = join_table(lat, pool_cd)          # nflats x Pc
    Hcd = H[Tc[carr]]                       # Pc x Pc : H(c u d)
    Hc = H[carr]
    cache = {}

    def J(*fs):
        key = tuple(sorted(set(fs)))
        if key not in cache:
            es = []
            for f in key:
                es += lat.gens_of(f)
            cache[key] = lat.cl_ids(es)
        return cache[key]
    cands = []
    pa = list(pool_ab)
    for ia in range(len(pa)):
        a = pa[ia]
        for ib in range(ia + 1, len(pa)):
            b = pa[ib]
            ab = J(a, b)
            if ab == a or ab == b:
                continue
            const = -H[a] - H[b] + H[ab]
            u = H[Tc[a]] + H[Tc[b]] - H[Tc[ab]]
            Mx = const + u[:, None] + u[None, :] - Hcd
            np.fill_diagonal(Mx, 1)
            for ic, id_ in np.argwhere(Mx < -tol):
                if ic < id_:
                    c_, d_ = pool_cd[ic], pool_cd[id_]
                    if c_ in (a, b) or d_ in (a, b):
                        continue
                    cands.append((Mx[ic, id_], a, b, c_, d_))
    cands.sort()
    cands = cands[:maxquads]
    if verbose:
        print(f"  Ingleton-violating quadruples used: {len(cands)} ({time.time()-t0:.1f}s)", flush=True)
    out, seen = [], set()

    def consider(row, info):
        val = sum(wt * H[f] for f, wt in row.items())
        if val < -tol:
            key = tuple(sorted(row.items()))
            if key not in seen:
                seen.add(key)
                out.append((val, row, info))

    def Hj(*fs):
        return H[J(*fs)]
    for ing, x, y, zz, ww in cands:
        roles = []
        for (p1, p2) in ((x, y), (y, x)):
            for (q1, q2) in ((zz, ww), (ww, zz)):
                roles.append(('abcd', p1, p2, q1, q2))
                roles.append(('acbd', p1, q1, p2, q2))
        for (variant, a, b, c, d) in roles:
            if variant == 'abcd':
                for s in s4:
                    consider(matus_row(s, a, b, c, d, J), ('M4', s, a, b, c, d))
            ab = J(a, b)
            ing_val = sum(wt * H[f] for f, wt in (ingleton_terms(a, b, c, d, J) if variant == 'abcd'
                                                   else ingleton_terms(a, c, b, d, J)).items())
            Iacb = Hj(a, b) + Hj(c, b) - Hj(a, b, c) - H[b]
            Iabc = Hj(a, c) + Hj(b, c) - Hj(a, b, c) - H[c]
            Ibca = Hj(b, a) + Hj(c, a) - Hj(a, b, c) - H[a]
            Haz = H[Tc[a]]; Hbz = H[Tc[b]]; Habz = H[Tc[ab]]
            Ibz_a = H[ab] + Haz - Habz - H[a]
            Iaz_b = H[ab] + Hbz - Habz - H[b]
            Iab_z = Haz + Hbz - Habz - Hc
            for k in ks:
                kk = k * (k - 1) // 2
                vM = Ibz_a + k * (ing_val + Iaz_b + Iab_z) + kk * (Iacb + Iabc)
                vC = Iab_z + k * (ing_val + Iaz_b + Ibz_a) + kk * (Iacb + Ibca)
                for fam, vec in (('M', vM), ('C', vC)):
                    for iz in np.nonzero(vec < -tol)[0][:5]:
                        z = pool_cd[iz]
                        consider(five_row(fam, k, a, b, c, d, z, variant, J), (fam, k, variant, a, b, c, d, z))
    out.sort(key=lambda t: t[0])
    if verbose:
        print(f"  violated rows: {len(out)}, worst {out[0][0] if out else None} ({time.time()-t0:.1f}s)", flush=True)
    return out[:maxcuts]
