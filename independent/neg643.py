#!/usr/bin/env python3
"""Negative tests for certificates in the format read by checker/check3.py: each perturbation must be rejected by BOTH check3.py
(subprocess, nonzero exit or no PASS) and indep3.py (in-process).  Usage: neg643.py CERT.json"""
import copy
import json
import os
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import indep3  # noqa: E402

CERT = os.path.expanduser(sys.argv[1])
CHECK3 = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'checker', 'check3.py')
TMP = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'negtmp643')
os.makedirs(TMP, exist_ok=True)
base = json.load(open(CERT))
DEN = Fraction(base['claimed_lambda']).denominator
eps = Fraction(1, DEN)
tests = []


def T(name, fn, inj=True):
    C = copy.deepcopy(base)
    fn(C)
    tests.append((name, C, inj))


def idx(t, k=0, cp=None):
    L = [i for i, r in enumerate(base['rows']) if r['type'] == t and (cp is None or r.get('copy') == cp)]
    return L[k % len(L)] if L else None


def setm(i, f):
    def g(C):
        C['rows'][i]['mult'] = str(f(Fraction(C['rows'][i]['mult'])))
    return g


def drop(i):
    def g(C):
        del C['rows'][i]
    return g


def setkey(i, key, val):
    def g(C):
        C['rows'][i][key] = val
    return g


T('identity (unperturbed, must PASS)', lambda C: None)
T('sub row mult * 1001/1000', setm(idx('sub'), lambda m: m * Fraction(1001, 1000)))
_iS = idx('g_h11') if idx('g_h11') is not None else idx('bsum')
T(f"S-row ({base['rows'][_iS]['type']}) mult - eps", setm(_iS, lambda m: m - eps))
T('claimed lambda - eps', lambda C: C.__setitem__('claimed_lambda', str(Fraction(C['claimed_lambda']) - eps)))
T('claimed lambda + eps', lambda C: C.__setitem__('claimed_lambda', str(Fraction(C['claimed_lambda']) + eps)))
for t in ('sub', 'merge', 'ident', 'g_link', 'g_concx', 'g_concy', 'ci', 'dpair', 'bsum', 'g_h11', 'g_monox'):
    i = idx(t)
    if i is not None:
        T(f'drop first {t} row (#{i})', drop(i))
i_id = [i for i, r in enumerate(base['rows']) if r['type'] == 'ident' and r['ij'] == [2, 0]]
if i_id:
    T('ident (2,0) relabelled (1,1)', setkey(i_id[0], 'ij', [1, 1]))
i_id1 = [i for i, r in enumerate(base['rows']) if r['type'] == 'ident' and r.get('copy') == 1]
if i_id1:
    T('ident row moved from copy 1 to copy 0', setkey(i_id1[0], 'copy', 0))
Wv = [k for k, v in enumerate(base['config']['vertices']) if v['type'] == 'W']
if Wv:
    k = Wv[0]
    a, b = base['config']['vertices'][k]['ij']
    T(f'W law ({a},{b}) -> ({b},{a})', lambda C: C['config']['vertices'][k].__setitem__('ij', [b, a]))
    T(f'W law ({a},{b}) -> ({a + 1},{b})', lambda C: C['config']['vertices'][k].__setitem__('ij', [a + 1, b]))
im = idx('merge')
T('merge perm maps x0 -> y1 (not an automorphism)', setkey(im, 'perm', [[0, 3], [1, 2], [2, 1], [3, 0]]))
T('merge perm moves W', setkey(im, 'perm', [[0, 2], [1, 3], [2, 0], [3, 1], [4, 0]]))
ib = idx('bsum')
T('bsum on x0 + x1 (not in X+Y)', setkey(ib, 'f', ['1', '0', '1', '0', '0']))
T('bsum moved to the other copy', setkey(ib, 'copy', 1 - int(base['rows'][ib]['copy'])))
T('grid depth 12 -> 11', lambda C: C.__setitem__('grid_depth', int(C['grid_depth']) - 1))
ic = idx('ci')
T('ci with old = half of a D vertex', lambda C: (C['rows'][ic].__setitem__('old', [0]), C['rows'][ic].__setitem__('new', [2, 3])))
T('ci with new = y0, old = x0 (dependent)', lambda C: (C['rows'][ic].__setitem__('old', [0]), C['rows'][ic].__setitem__('new', [1])))
i1 = idx('sub', 0, cp=1)
T('a copy-1 sub row moved to copy 0', setkey(i1, 'copy', 0))
ig = idx('g_concx')
T('negative g_concx multiplier', setm(ig, lambda m: -m))
il = idx('g_link')
T('g_link row retyped g_concx', setkey(il, 'type', 'g_concx'))
T("no injectivity rule (indep only)", lambda C: None, inj=False)

RSW = [i for i, r in enumerate(base['rows']) if r['type'] == 'rshare' and r.get('wmap')
       and any(Fraction(g[4]) != 0 or Fraction(g[5]) != 0 for g in r['G'])]
if RSW:
    iw = RSW[0]
    T(f'rshare row {iw}: wmap to same-law W ([[4,4],[5,5]])', setkey(iw, 'wmap', [[4, 4], [5, 5]]))
    T(f'rshare row {iw}: non-injective wmap ([[4,5],[5,5]])', setkey(iw, 'wmap', [[4, 5], [5, 5]]))
    T(f'rshare row {iw}: wmap removed (generators use W)', lambda C: C['rows'][iw].pop('wmap'))
    def flip_w(C):
        G2 = []
        for g in C['rows'][iw]['G']:
            g2 = list(g)
            for c in (4, 5):
                if Fraction(g2[c]) != 0:
                    g2[c] = str(-Fraction(g2[c]))
            G2.append(g2)
        C['rows'][iw]['G'] = G2
    T(f'rshare row {iw}: W coefficients of the generators negated (wrong-sign phi emulation)', flip_w)
    def dup_rs(C):
        r2 = copy.deepcopy(C['rows'][iw]); r2['mult'] = str(Fraction(r2['mult']) / 3 if Fraction(r2['mult']) != 0 else Fraction(1, 7))
        C['rows'].append(r2)
    T(f'rshare row {iw}: duplicated with mult/3 (unbalanced)', dup_rs)
    T(f'drop rshare row {iw}', drop(iw))
im2 = [i for i, r in enumerate(base['rows']) if r['type'] == 'merge']
if im2:
    T('merge row with w<->v injected (W s of different laws)', setkey(im2[0], 'perm', [[0, 2], [1, 3], [2, 0], [3, 1], [4, 5], [5, 4]]))


Wcoords = [int(v['coords'][0]) for v in base['config']['vertices'] if v['type'] == 'W']
if len(Wcoords) >= 2:
    w_, v_ = Wcoords[0], Wcoords[1]
    MW = [i for i, r in enumerate(base['rows']) if r['type'] == 'merge' and any(int(a) == w_ and int(b) == v_ for a, b in r['perm'])]
    if MW:
        T('w<->v merge rewritten as w<->x0 (W to D coordinate)', setkey(MW[0], 'perm', [[w_, 0], [0, w_]]))
        T('w<->v merge rewritten as w->v, v->x0, x0->w', setkey(MW[0], 'perm', [[w_, v_], [v_, 0], [0, w_]]))
    k2 = [k for k, v in enumerate(base['config']['vertices']) if v['type'] == 'W'][1]
    T('second W law (1,0) -> (0,1) (w<->v merges then permute W s of different laws)',
      lambda C: C['config']['vertices'][k2].__setitem__('ij', [0, 1]))
    IW = [i for i, r in enumerate(base['rows']) if r['type'] == 'ident' and Fraction(r['f'][w_]) == 1 and Fraction(r['f'][v_]) == 1
          and sum(1 for a in r['f'] if Fraction(a) != 0) == 2]
    if IW:
        fwv = list(base['rows'][IW[0]]['f']); fwv[v_] = '-1'
        T('ident w+v rewritten as w-v with ij (2,0)', setkey(IW[0], 'f', fwv))
        T('ident w+v relabelled (1,1)', setkey(IW[0], 'ij', [1, 1]))


RS = [i for i, r in enumerate(base['rows']) if r['type'] == 'rshare']
if RS:
    ir = RS[0]
    def rs_swap_no_neg(C):
        # replace the row by its image under a WRONG map (x <-> y without negation) expressed as a G change
        G = C['rows'][ir]['G']
        G2 = []
        for g in G:
            g2 = list(g)
            for x_, y_ in ((0, 1), (2, 3)):
                g2[x_], g2[y_] = g[y_], g[x_]
            G2.append(g2)
        C['rows'][ir]['G'] = G2
    T(f'rshare row {ir}: generators replaced by x<->y swapped versions', rs_swap_no_neg)
    T(f'rshare row {ir}: multiplier scaled 1001/1000', setm(ir, lambda m: m * Fraction(1001, 1000)))
    T(f'drop rshare row {ir}', drop(ir))
    def rs_add_w(C):
        g = list(C['rows'][ir]['G'][0]); g[-1] = '1'; C['rows'][ir]['G'][0] = g
    T(f'rshare row {ir}: W coordinate added to a generator', rs_add_w)


# W-form specific perturbations (W coordinate = the coordinate of the first W vertex)
if Wv:
    wc = int(base['config']['vertices'][Wv[0]]['coords'][0])
    NCo = int(base['config']['coords'])
    # a sub row whose i or j involves W with at least 3 nonzero coefficients: flip the sign of one D coordinate
    cand = [i for i, r in enumerate(base['rows']) if r['type'] == 'sub' and
            sum(1 for a in r['i'] if Fraction(a) != 0) >= 3 and Fraction(r['i'][wc]) != 0]
    if cand:
        iw = cand[0]
        fi = list(base['rows'][iw]['i'])
        kflip = next(c for c in range(NCo) if c != wc and Fraction(fi[c]) != 0)
        fi2 = list(fi); fi2[kflip] = str(-Fraction(fi[kflip]))
        T(f'W-form in sub row {iw}: flip sign of coordinate {kflip}', setkey(iw, 'i', fi2))
    idw = [i for i, r in enumerate(base['rows']) if r['type'] == 'ident' and Fraction(r['f'][wc]) != 0
           and sum(1 for a in r['f'] if Fraction(a) != 0) >= 2]
    if idw:
        iiw = idw[0]
        f = list(base['rows'][iiw]['f'])
        kk_ = next(c for c in range(NCo) if c != wc and Fraction(f[c]) != 0)
        f2 = list(f); f2[kk_] = '-1'
        T(f'ident row {iiw} on a W-form with a minus sign', setkey(iiw, 'f', f2))
    fsum = ['0'] * NCo; fsum[0] = '1'; fsum[wc] = '1'
    T('bsum on x0 + w (both X-valued, not in X+Y)', setkey(ib, 'f', fsum))
    fdiff = ['0'] * NCo; fdiff[0] = '-1'; fdiff[wc] = '1'
    T('bsum retyped bdiff on w - x0 (not in X-Y)', lambda C: (C['rows'][ib].__setitem__('type', 'bdiff'), C['rows'][ib].__setitem__('f', fdiff)))


# pmerge-specific tests.  (1) Rule tests in isolation: append one pmerge row with multiplier 0 (it adds nothing to the
# identity, so only the rule check can reject it); controls that satisfy the rule must PASS.  (2) Real pmerge rows
# perturbed (identity-relevant).
PM = [i for i, r in enumerate(base['rows']) if r['type'] == 'pmerge']
if PM:
    vs = base['config']['vertices']
    Dv = [v['coords'] for v in vs if v['type'] == 'D']
    Wl = [(v['coords'][0], tuple(v['ij'])) for v in vs if v['type'] == 'W']
    NCo = int(base['config']['coords'])
    (x0, y0), (x1, y1) = Dv[0], Dv[1]
    wmu = [w for w, ij in Wl if ij == (1, 0)]

    def unit(*cs):
        f = ['0'] * NCo
        for c in cs:
            f[c] = '1'
        return f

    def addpm(G, perm, cp=0):
        def g(C):
            C['rows'].append({'type': 'pmerge', 'copy': cp, 'G': G, 'perm': perm, 'mult': '0'})
        return g
    for cp in (0, 1):
        if wmu:
            w = wmu[0]
            T(f'[cp{cp}] CONTROL pmerge mult 0: x0 <-> w (valid, must PASS)', addpm([unit(x0)], [[x0, w], [w, x0]], cp))
            T(f'[cp{cp}] pmerge mult 0: w (law mu) -> y0 (law nu)', addpm([unit(w)], [[w, y0], [y0, w]], cp))
            T(f'[cp{cp}] pmerge mult 0: G touches x0 and y0, x0 -> w only (vertex split)', addpm([unit(x0, y0)], [[x0, w], [w, x0]], cp))
            if len(wmu) > 1:
                T(f'[cp{cp}] CONTROL pmerge mult 0: w <-> w2 (same law, must PASS)', addpm([unit(w)], [[w, wmu[1]], [wmu[1], w]], cp))
        T(f'[cp{cp}] pmerge mult 0: x0 -> y0 (law mu -> nu)', addpm([unit(x0)], [[x0, y0], [y0, x0]], cp))
        T(f'[cp{cp}] pmerge mult 0: x0 -> x1 with y1 kept (two vertices into one)', addpm([unit(x0, y1)], [[x0, x1], [x1, x0]], cp))
        T(f'[cp{cp}] pmerge mult 0: D0 -> D1 crossed (x0 -> y1, y0 -> x1)', addpm([unit(x0), unit(y0)], [[x0, y1], [y0, x1], [y1, x0], [x1, y0]], cp))
        T(f'[cp{cp}] CONTROL pmerge mult 0: y0 <-> y1 (same law, must PASS)', addpm([unit(y0)], [[y0, y1], [y1, y0]], cp))
        T(f'[cp{cp}] pmerge mult 0: not a permutation', addpm([unit(x0)], [[x0, x1], [x1, x1]], cp))
    for cp in (0, 1):
        L = [i for i in PM if base['rows'][i].get('copy') == cp]
        if not L:
            continue
        ip = L[0]
        rp = base['rows'][ip]
        T(f'pmerge row {ip} (cp{cp}): multiplier * 1001/1000', setm(ip, lambda m: m * Fraction(1001, 1000)))
        T(f'drop pmerge row {ip} (cp{cp})', drop(ip))
        # replace the swap partner of the touched lone x coordinate by the y coordinate of the same D vertex
        sup = sorted({c for g in rp['G'] for c in range(NCo) if Fraction(g[c]) != 0})
        lone_x = [c for c in sup if any(c == d[0] for d in Dv) and not any(c == d[0] and d[1] in sup for d in Dv)]
        if lone_x:
            c = lone_x[0]
            yc = next(d[1] for d in Dv if d[0] == c)
            T(f'pmerge row {ip} (cp{cp}): perm x{c} <-> y{yc} instead (law mismatch)', setkey(ip, 'perm', [[c, yc], [yc, c]]))
            G2 = [list(g) for g in rp['G']]
            G2[0][yc] = '1' if Fraction(G2[0][yc]) == 0 else str(Fraction(G2[0][yc]) + 1)
            T(f'pmerge row {ip} (cp{cp}): generator also touches y{yc} (vertex split)', setkey(ip, 'G', G2))


# xshare-specific tests: rule tests in isolation (appended rows with multiplier 0; controls must PASS), then real rows.
XS = [i for i, r in enumerate(base['rows']) if r['type'] == 'xshare']
if XS:
    vs = base['config']['vertices']
    Dv = [v['coords'] for v in vs if v['type'] == 'D']
    Wl = [(v['coords'][0], tuple(v['ij'])) for v in vs if v['type'] == 'W']
    NCo = int(base['config']['coords'])
    (x0, y0), (x1, y1) = Dv[0], Dv[1]
    wmu = [w for w, ij in Wl if ij == (1, 0)]

    def unitx(*cs):
        f = ['0'] * NCo
        for c in cs:
            f[c] = '1'
        return f

    def addxs(G, mp):
        def g(C):
            C['rows'].append({'type': 'xshare', 'G': G, 'map': mp, 'mult': '0'})
        return g
    T("CONTROL xshare mult 0: x0' -> -y0 (mu' = law(-Y1); must PASS)", addxs([unitx(x0)], [[x0, y0]]))
    T("CONTROL xshare mult 0: pair (x0', y0') -> (-y1, -x1) (must PASS)", addxs([unitx(x0, y0)], [[x0, y1], [y0, x1]]))
    if wmu:
        w = wmu[0]
        T("CONTROL xshare mult 0: y0' -> -w (nu' = law(-X1), w ~ mu; must PASS)", addxs([unitx(y0)], [[y0, w]]))
        T("CONTROL xshare mult 0: w' -> -y1 (w' ~ mu' = law(-Y1); must PASS)", addxs([unitx(w)], [[w, y1]]))
        if len(wmu) > 1:
            T("xshare mult 0: w' -> -w2 (law mu' vs law of -w2 = nu'; not transposed)", addxs([unitx(w)], [[w, wmu[1]]]))
        T("xshare mult 0: pair (x0', y0') -> x0', -w split into two vertices", addxs([unitx(x0, y0)], [[x0, y0], [y0, w]]))
    T("xshare mult 0: x0' -> -x1 (not transposed)", addxs([unitx(x0)], [[x0, x1]]))
    T("xshare mult 0: pair (x0', y0') -> (-x1, -y1) (not swapped)", addxs([unitx(x0, y0)], [[x0, x1], [y0, y1]]))
    T("xshare mult 0: x0', y1' both into D0 (two vertices into one)", addxs([unitx(x0, y1)], [[x0, y0], [y1, x0]]))
    T("xshare mult 0: map misses part of the support", addxs([unitx(x0, y0)], [[x0, y1]]))
    T("xshare mult 0: map defines a coordinate twice", addxs([unitx(x0)], [[x0, y0], [x0, y1]]))
    ix = XS[0]
    rx = base['rows'][ix]
    T(f'xshare row {ix}: multiplier * 1001/1000', setm(ix, lambda m: m * Fraction(1001, 1000)))
    T(f'drop xshare row {ix}', drop(ix))
    # change one map entry to a target of the wrong law type (an x coordinate replaced by the y of the same vertex)
    mp = [[int(a), int(b)] for a, b in rx['map']]
    role = {}
    for k, (xx, yy) in enumerate(Dv):
        role[xx], role[yy] = ('x', k), ('y', k)
    for e in mp:
        if e[1] in role:
            kind, k = role[e[1]]
            e2 = Dv[k][1] if kind == 'x' else Dv[k][0]
            if all(e2 != f[1] for f in mp):
                mp2 = [list(f) for f in mp]
                mp2[mp.index(e)] = [e[0], e2]
                T(f'xshare row {ix}: map {e[0]}->{e[1]} changed to {e[0]}->{e2} (wrong law)', setkey(ix, 'map', mp2))
                break
    T(f'xshare row {ix}: retyped as pmerge with perm = map (one copy instead of two)',
      lambda C: (C['rows'][ix].__setitem__('type', 'pmerge'), C['rows'][ix].__setitem__('copy', 0),
                 C['rows'][ix].__setitem__('perm', [[a, b] for a, b in rx['map']] + [[b, a] for a, b in rx['map'] if [b, a] not in rx['map']])))
    T(f'INFO xshare row {ix}: generators negated (same flats; expected PASS)',
      setkey(ix, 'G', [[str(-Fraction(a)) for a in g] for g in rx['G']]))


NS5 = [i for i, r in enumerate(base['rows']) if r['type'] == 'five']
NS4 = [i for i, r in enumerate(base['rows']) if r['type'] == 'matus4']
if NS5:
    i5 = NS5[0]
    r5 = base['rows'][i5]
    T(f"five row {i5}: k {r5['k']} -> {r5['k'] + 1}", setkey(i5, 'k', r5['k'] + 1))
    if r5['k'] > 1:
        T(f"five row {i5}: k {r5['k']} -> {r5['k'] - 1}", setkey(i5, 'k', r5['k'] - 1))
    T(f"five row {i5}: variant {r5['variant']} swapped", setkey(i5, 'variant', 'acbd' if r5['variant'] == 'abcd' else 'abcd'))
    T(f"five row {i5}: family {r5['fam']} swapped", setkey(i5, 'fam', 'C' if r5['fam'] == 'M' else 'M'))
    T(f"five row {i5}: variables a <-> b", lambda C: C['rows'][i5].__setitem__('vars', [r5['vars'][1], r5['vars'][0]] + r5['vars'][2:]))
    T(f"five row {i5}: variables c <-> z", lambda C: C['rows'][i5].__setitem__('vars', r5['vars'][:2] + [r5['vars'][4], r5['vars'][3], r5['vars'][2]]))
    T(f"five row {i5}: multiplier negated", setm(i5, lambda m: -m))
    T(f"drop five row {i5}", drop(i5))
if NS4:
    i4 = NS4[0]
    r4 = base['rows'][i4]
    T(f"matus4 row {i4}: s {r4['s']} -> {r4['s'] + 1}", setkey(i4, 's', r4['s'] + 1))
    T(f"matus4 row {i4}: s {r4['s']} -> {r4['s'] - 1}", setkey(i4, 's', r4['s'] - 1))
    T(f"matus4 row {i4}: a <-> b", lambda C: C['rows'][i4].__setitem__('vars', [r4['vars'][1], r4['vars'][0]] + r4['vars'][2:]))
    T(f"matus4 row {i4}: c <-> d", lambda C: C['rows'][i4].__setitem__('vars', r4['vars'][:2] + [r4['vars'][3], r4['vars'][2]]))
    T(f"matus4 row {i4}: multiplier * 1001/1000", setm(i4, lambda m: m * Fraction(1001, 1000)))
    T(f"drop matus4 row {i4}", drop(i4))



def run(t):
    name, C, inj = t
    path = os.path.join(TMP, f'n{abs(hash(name))}.json')
    json.dump(C, open(path, 'w'))
    if inj:
        r = subprocess.run([sys.executable, '-I', CHECK3, path], capture_output=True, text=True)
        c3 = 'PASS' if (r.returncode == 0 and 'PASS' in r.stdout) else 'FAIL'
    else:
        c3 = 'n/a'
    try:
        ok, info = indep3.check(C, inj=inj)
        ind = 'PASS' if ok else 'FAIL'
    except Exception as e:  # noqa: BLE001
        ind, info = 'FAIL', f'{type(e).__name__}: {e}'
    os.remove(path)
    return name, c3, ind, str(info)[:100]


with ThreadPoolExecutor(max_workers=4) as ex:
    res = list(ex.map(run, tests))
bad = 0
for name, c3, ind, info in res:
    exp = 'PASS' if name.startswith('identity') else 'FAIL'
    flag = ''
    if (c3 not in (exp, 'n/a')) or ind != exp:
        flag = '   <-- UNEXPECTED'
        bad += 1
    print(f'{name:55s} check3={c3:4s} indep={ind:4s}{flag}')
    if exp == 'FAIL' and ind == 'FAIL':
        print(f'      indep: {info}')
print(f'tests: {len(res)}; unexpected outcomes: {bad}')
