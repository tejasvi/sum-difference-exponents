#!/usr/bin/env python3
"""Independent exact checker for two-set exponent certificates (cert3 format: mutually independent vertices).

Usage: python3 check3.py CERT.json

Claim checked: for all finite nonempty X, Y in Z,  log|X - Y| <= lambda * log|X + Y|.

Setting (definitions shared with the search code only through this documentation).
  Gamma in X x Y: one pair per difference, (X1, Y1) uniform on Gamma, L = log|X-Y| = H(X1, Y1);
  S = log|X+Y|.  Configuration (config.vertices, built in this order): D vertices (x_k, y_k), copies of (X1, Y1),
  and W vertices (one coordinate w with law mu^{*i} * nu^{*j}, ij given), each independent of all earlier
  vertices; C vertices (conditional copies): coordinates c_1..c_m with src coordinates s_1..s_m and given forms
  V (src and V use only coordinates of earlier vertices): the joint law of (c, V) equals that of (s, V), and c is
  conditionally independent of all earlier coordinates given V.  (Such an extension exists: draw c from the
  conditional law of s given V.)  C coordinates are X-valued (Y-valued) when their src coordinate is.
  Certificates with C vertices have a single configuration.  Linear forms: rational vectors f over the
  coordinates, f(v) = sum f_c v_c.
  Copy 0 is this configuration for Gamma; copy 1 is the same configuration for the reflected pair
  (X', Y') = (-Y, -X) with Gamma' = {(-y, -x) : (x, y) in Gamma}, which has the same L and S.
  Grid: h(i, j) = H(mu^{*i} * nu^{*j}) for the marginals mu, nu of Gamma (sums of independent variables);
  for the reflected pair the grid is h'(i, j) = h(j, i).
  cl(G): smallest subspace containing the forms G and closed under: if x_k - y_k (D vertex k) lies in
  it then so do x_k and y_k.  H-terms are keyed by (copy, cl(G)) (canonical RREF basis); H(cl G) = H(G).
Row types, each written as an expression R that is >= 0 (inequality rows, mult >= 0 required) or = 0
(equality rows, any mult), in terms of H-terms, h(i,j), L, S:
  sub      I(i; j | K) = H(K+i) + H(K+j) - H(K+i+j) - H(K)                    (Shannon)
  mono     H(K+i) - H(K)                                                       (Shannon)
  ci       H(old u new) - H(old) - H(new) = 0, new = coords of one D or W vertex, old = coords of all earlier
           vertices                                                            (independence)
  cci      H(old u new) + H(V) - H(old) - H(V u new) = 0, new = coords of C vertex k, V = its given forms,
           old = coords of all earlier vertices                                (conditional independence)
  cmerge   H(cl psi G) - H(cl G) = 0 for C vertex k: every generator g of G lies in span(c_1..c_m, V, coordinates
           of D/W vertices listed after k); psi(g) = g with the coefficient of c_i moved to s_i  ((c, V) and (s, V)
           have the same law, and the later D/W vertices are independent of both)
  merge    H(cl tau G) - H(cl G) = 0, tau = coordinate permutation mapping D vertices to D vertices
           (x to x, y to y) and W vertices to W vertices with the same law (all vertices mutually independent,
           D copies iid, equal-law W's iid: the joint law is invariant).  With C vertices: tau fixes the C
           coordinates and G does not involve them (the D and W coordinates alone are mutually independent).
  pmerge   H(cl tau G) - H(cl G) = 0, tau a coordinate permutation fixing C coordinates such that G avoids the C
           coordinates and, on the support of G:
           the touched coordinates of each vertex map into a single vertex, distinct vertices to distinct vertices,
           and marginal laws agree: a D vertex touched in both coordinates maps to a D vertex (x to x, y to y); a lone
           x_k, or a W with law mu, maps to an x coordinate or a W with law mu; a lone y_k, or a W with law nu, to a
           y coordinate or a W with law nu; other W's to W's of the same law.  (The touched coordinates of distinct
           vertices are independent, so the joint law of the support equals that of its image.)
  xshare   H_0(cl tau G) - H_1(cl G) = 0 (configuration 0; G and tau G avoid C coordinates), tau(c) = -map(c) on
           the support U of G:
           a copy-1 pair (x'_k, y'_k) touched in both coordinates maps to (-y_m, -x_m) of one copy-0 D vertex m; a lone
           x'_k or copy-1 W with law mu (copy 1: law mu' = law(-Y1)) maps to -(y_m) or -(W with law nu); a lone y'_k
           or copy-1 W with law nu (nu' = law(-X1)) to -(x_m) or -(W with law mu); a copy-1 W with law (i,j) otherwise
           to -(W with law (j,i)); distinct copy-1 vertices to distinct copy-0 vertices.  (Copy 1's touched parts are
           independent with these marginal laws; so are their images in copy 0.)
  bsum     S - H(f),  f = x + y, x X-valued, y Y-valued                       (f in X+Y)
  bdiff    L - H(f),  f = x - y                                                (f in X-Y)
  batom    S - H(f),  f = x or y                                               (|X|, |Y| <= |X+Y|)
           X-valued coordinates: x_k of D vertices and W vertices with law mu (ij = (1,0));
           Y-valued: y_k and W vertices with law nu (ij = (0,1)).  With C vertices, f (up to sign) may also be
           any form in the closure computed by valued_forms(): images tau(g) of X-, Y-, (X+Y)-, (X-Y)-valued forms
           g in span(src, V) under a C vertex's map (tau g has the law of g), and sums / differences of
           X-valued and Y-valued forms.
  dpair    L - H(x_k, y_k) = 0                                                 (Gamma uniform)
  ident    h(i,j) - H(f) = 0 (copy 0), h(j,i) - H(f) = 0 (copy 1), f = sum of x_k (k in I), y_k (k in J)
           and w (W in Q), I, J disjoint, i = |I| + sum_Q i_W, j = |J| + sum_Q j_W   (independent sums;
           f does not involve C coordinates)
  g_h00    -h(0,0) = 0;   g_nonneg h(i,j);   g_monox h(i+1,j) - h(i,j);   g_monoy h(i,j+1) - h(i,j)
  g_concx  2h(i+1,j) - h(i,j) - h(i+2,j);   g_concy 2h(i,j+1) - h(i,j) - h(i,j+2)   (Madiman)
  g_link   h(i+1,j) + h(i,j+1) - h(i,j) - L                                    (coupled Ruzsa)
  g_h11    S - h(1,1)                                                          (support)
  multigrid families (per copy cp, f = a x + b y with (a,b) in {(1,1),(1,-1)}):
           g(i,j) := H(f(X1,Y1) + V_ij), V_ij ~ mu^{*i} * nu^{*j} independent of (X1,Y1) (copy 1: the reflected
           pair, its own marginals, and hcp(i,j) := h(j,i); copy 0: hcp = h).
  mg_nonneg g(i,j);  mg_monox g(i+1,j) - g(i,j);  mg_monoy g(i,j+1) - g(i,j)                 (independent summand)
  mg_concx 2g(i+1,j) - g(i,j) - g(i+2,j);  mg_concy likewise                                   (Madiman)
  mg_geh   g(i,j) - hcp(i,j)                                                    (H(A+V) >= H(V), A indep. of V)
  mg_le1   hcp(i+1,j) + hcp(0,1) - g(i,j)        (f(X,Y)+V is a function of (X+V, Y) for both families)
  mg_ge1   g(i,j) + hcp(0,1) - hcp(i+1,j)        (X+V is a function of (f(X,Y)+V, Y) for both families)
  mg_le2   hcp(i,j+1) + hcp(1,0) - g(i,j)        (family (1,1) only: X+Y+V is a function of (Y+V, X))
  mg_ge2   g(i,j) + hcp(1,0) - hcp(i,j+1)        (family (1,1) only: Y+V is a function of (X+Y+V, X))
  mgident  g(i,j) - H(F) = 0, F = a x_k + b y_k (one D vertex k) + 0/1 coordinates of other D vertices (<= 1 per
           vertex) + W's with coefficient 1; i, j count the added mu- and nu-summands (W counts its ij)
  share    H_0(cl psi(G)) - H_c(cl G) = 0 for G supported on D coordinates; psi = identity if copy c is
           unreflected, psi = phi if reflected (several configurations share the D vertices on one space)
  rshare   H_0(cl phi(G)) - H_1(cl G) = 0 for G supported on D coordinates, phi: x_k -> -y_k, y_k -> -x_k
           (copy 1's D vertices realised as (-Y_k, -X_k) of copy 0's D vertices on one probability space).
           Optional wmap [[a, b], ...] (configuration 0, injective a -> b, W vertex b has the transposed law of W
           vertex a): G may also use the coordinates a, and phi(w_a) = -w_b.  (Copy 1's W_a has law
           mu'^{*i} nu'^{*j} = law of -(mu^{*j} nu^{*i}) since mu' = law(-Y), nu' = law(-X); realising it as -W_b
           keeps all of copy 1's vertices mutually independent with the right laws.)
  signed grid: g(t), t = (a, a', b, b'), := H(sum of independent variables: a with law mu, a' with the law of -X1,
           b with law nu, b' with the law of -Y1); g(a,a',b,b') = g(a',a,b',b) (negation), terms keyed by the smaller.
  sg_h     h(a,b) - g(a,0,b,0) = 0
  sg_nonneg g(t);  sg_mono g(t+d) - g(t) (independent summand);  sg_conc 2g(t+d) - g(t) - g(t+2d) (Madiman);
           d = one unit vector (one more summand of one of the four types)
  sg_link  g(t+dx) + g(t+dy) - g(t) - L, (dx, dy) = (mu, nu) or (-mu, -nu): with V independent of (X1, Y1) and of
           type t, (X1 + V, Y1 + V) (resp. (-X1 + V, -Y1 + V)) determines (X1, Y1, V) since X1 - Y1 determines (X1, Y1)
  sg_diff  L - g(1,0,0,1)   (X1 - Y2 with independent copies lies in X - Y)
  sg_ident g(t) - H(f) = 0: f has coefficients in {-1,0,1}, at most one nonzero coordinate per D vertex, W's with
           coefficient +-1, no other coordinates; copy 0: t counts +x, -x, +y, -y (a W with law mu^{*i} nu^{*j} adds
           i to the x count and j to the y count of its sign); copy 1: with (n1, n2, n3, n4) these counts in copy 1's
           own coordinates, t = (n4, n3, n2, n1) (x'_k has the law of -Y1, y'_k the law of -X1)
  matus4   M_s(a,b,c,d) = I(b;c|a) + s[abcd] + C(s+1,2)(I(a;c|b) + I(a;b|c))   (Matus 2007)
  five     M_k / C_k (Csirmaz-Csirmaz Thm 22, (31)) with Ingleton [abcd] or [acbd]:
           M_k = I(b;z|a) + k(Ing + I(a;z|b) + I(a;b|z)) + C(k,2)(I(a;c|b) + I(a;b|c))
           C_k = I(a;b|z) + k(Ing + I(a;z|b) + I(b;z|a)) + C(k,2)(I(a;c|b) + I(b;c|a))
           [abcd] = -I(a;b) + I(a;b|c) + I(a;b|d) + I(c;d); variables a..z are cl(generator lists),
           joint variables are closures of unions.
Identity checked: sum_rows mult * R == lambda * S - L exactly.  Then lambda*S - L >= 0, i.e. L <= lambda S.
Only the Python standard library is used.
"""
import json, sys
from fractions import Fraction

NC = None          # number of coordinates (set from the certificate)
DV = []            # D vertices (x, y)
WV = []            # W vertices (coord, i, j)
CV = []            # C vertices (coords, src, given forms), in vertex order


def vec(f):
    v = [Fraction(x) for x in f]
    assert len(v) == NC
    return v


def unitv(c):
    return [Fraction(1 if i == c else 0) for i in range(NC)]


def rref(vs):
    rows = []
    for v in vs:
        v = list(v)
        for p, r in rows:
            if v[p] != 0:
                cf = v[p]
                v = [a - cf * b for a, b in zip(v, r)]
        piv = next((i for i, a in enumerate(v) if a != 0), None)
        if piv is None:
            continue
        cf = v[piv]
        v = [a / cf for a in v]
        new = []
        for p, r in rows:
            if r[piv] != 0:
                c2 = r[piv]
                r = [a - c2 * b for a, b in zip(r, v)]
            new.append((p, r))
        new.append((piv, v))
        rows = sorted(new)
    return rows


def in_span(rows, v):
    v = list(v)
    for p, r in rows:
        if v[p] != 0:
            cf = v[p]
            v = [a - cf * b for a, b in zip(v, r)]
    return all(a == 0 for a in v)


_cl = {}


def closure_key(gens):
    key0 = tuple(tuple(g) for g in gens)
    if key0 in _cl:
        return _cl[key0]
    vs = [list(g) for g in gens]
    while True:
        rows = rref(vs)
        added = False
        for (x, y) in DV:
            d = [Fraction(0)] * NC
            d[x] = Fraction(1)
            d[y] = Fraction(-1)
            if rows and in_span(rows, d):
                for c in (x, y):
                    if not in_span(rows, unitv(c)):
                        vs.append(unitv(c))
                        added = True
        if not added:
            break
    rows = rref(vs)
    key = tuple(tuple(r) for p, r in rows)
    _cl[key0] = key
    return key


class Acc:
    def __init__(self):
        self.t = {}

    def add(self, term, c):
        if term is None or c == 0:
            return
        self.t[term] = self.t.get(term, Fraction(0)) + c


def Hterm(cp, gens):
    k = closure_key(gens)
    if not k:
        return None              # H(empty) = 0
    return ('H', cp, k)


def is_atom(f):
    nz = [(i, a) for i, a in enumerate(f) if a != 0]
    return len(nz) == 1 and nz[0][1] in (1, -1)


def xvalued():
    """Coordinates that are X-valued: x_k of D vertices, W vertices with law mu (ij = (1,0)), C coordinates
    copying an X-valued coordinate."""
    xs = {v[0] for v in DV} | {w for (w, a, b) in WV if (a, b) == (1, 0)}
    for cs, src, given in CV:
        xs |= {c for c, s in zip(cs, src) if s in xs}
    return xs


def yvalued():
    """Coordinates that are Y-valued: y_k of D vertices, W vertices with law nu (ij = (0,1)), C coordinates
    copying a Y-valued coordinate."""
    ys = {v[1] for v in DV} | {w for (w, a, b) in WV if (a, b) == (0, 1)}
    for cs, src, given in CV:
        ys |= {c for c, s in zip(cs, src) if s in ys}
    return ys


def ccoords():
    return {c for cs, src, given in CV for c in cs}


def solve_cols(cols, g):
    """Coefficients a with sum a_i cols[i] = g (columns linearly independent), or None if g is not in their span."""
    n = len(cols)
    rows = []                      # augmented rows: column vector entries + identity part
    for i, cvec in enumerate(cols):
        rows.append(list(cvec) + [Fraction(1 if j == i else 0) for j in range(n)])
    # eliminate on the first NC entries
    red = []
    for rw in rows:
        rw = list(rw)
        for p, rr in red:
            if rw[p] != 0:
                cf = rw[p]
                rw = [a - cf * b for a, b in zip(rw, rr)]
        piv = next((i for i in range(NC) if rw[i] != 0), None)
        assert piv is not None, "src coordinates and given forms must be linearly independent"
        cf = rw[piv]
        rw = [a / cf for a in rw]
        red = [(p, [a - rr[piv] * b for a, b in zip(rr, rw)]) if rr[piv] != 0 else (p, rr) for p, rr in red]
        red.append((piv, rw))
    v = list(g) + [Fraction(0)] * n
    for p, rr in red:
        if v[p] != 0:
            cf = v[p]
            v = [a - cf * b for a, b in zip(v, rr)]
    if any(v[i] != 0 for i in range(NC)):
        return None
    return [-x for x in v[NC:]]


def valued_forms():
    """Forms whose value lies in X (XA), Y (YA), X+Y (SP), X-Y (DF) almost surely: X-/Y-valued coordinates, sums
    and differences of an X-valued and a Y-valued form, and their images under the C vertices' maps tau
    (g in span(src, V), g = sum a_i s_i + sum b_j V_j  ->  tau g = sum a_i c_i + sum b_j V_j has the law of g)."""
    XA = [unitv(c) for c in sorted(xvalued())]
    YA = [unitv(c) for c in sorted(yvalued())]

    def add(S, g):
        if not any(h == g or h == [-a for a in g] for h in S):
            S.append(g)

    def pairs(SP, DF):
        for a in XA:
            for b in YA:
                add(SP, [x + y for x, y in zip(a, b)])
                add(DF, [x - y for x, y in zip(a, b)])
    SP, DF = [], []
    pairs(SP, DF)
    for cs, src, given in CV:
        cols = [unitv(s_) for s_ in src] + list(given)
        for S in (XA, YA, SP, DF):
            for g in list(S):
                co = solve_cols(cols, g)
                if co is None:
                    continue
                img = list(g)
                for i, (c, s_) in enumerate(zip(cs, src)):
                    img[s_] -= co[i]
                    img[c] += co[i]
                add(S, img)
        pairs(SP, DF)
    return XA, YA, SP, DF


def in_pm(f, S):
    return any(h == f or h == [-a for a in f] for h in S)


def xy_pair(f, sign):
    """f = +-(x + sign*y) with x X-valued and y Y-valued coordinates?"""
    nz = [(i, a) for i, a in enumerate(f) if a != 0]
    if len(nz) != 2:
        return False
    (i1, a1), (i2, a2) = nz
    xs = xvalued()
    ys = yvalued()
    for (xi, ax), (yi, ay) in (((i1, a1), (i2, a2)), ((i2, a2), (i1, a1))):
        if xi in xs and yi in ys and abs(ax) == 1 and abs(ay) == 1 and ax * ay == sign:
            return True
    return False


def grid_form(f):
    """Return (i, j) if f is a 0/1 combination with at most one coordinate per D vertex (plus any W's)."""
    if any(a not in (0, 1) for a in f) or any(f[c] != 0 for c in ccoords()):
        return None
    i = j = 0
    for (x, y) in DV:
        if f[x] == 1 and f[y] == 1:
            return None
        i += int(f[x] == 1)
        j += int(f[y] == 1)
    for (w, wi, wj) in WV:
        if f[w] == 1:
            i += wi
            j += wj
    if i + j == 0:
        return None
    return (i, j)


def check(path):
    global NC, DV, WV, CV
    C = json.load(open(path))
    lam = Fraction(C['claimed_lambda'])
    M = int(C['grid_depth'])
    # one or several configurations; copy c belongs to configuration c // 2, reflected iff c % 2 == 1.
    # All configurations must have the same coordinates and the same D vertices (they may differ in W laws);
    # they are realised on one probability space (D vertices shared, each configuration's W independent).
    CFGS = C['configs'] if 'configs' in C else [C['config']]
    NC = int(CFGS[0]['coords'])
    DVs, WVs, VCs = [], [], []
    CVd = {}           # vertex index -> (coords, src, given) for C vertices (single configuration only)
    VT = [v['type'] for v in CFGS[0]['vertices']]
    for cf in CFGS:
        assert int(cf['coords']) == NC
        dv, wv, cv, seen = [], [], [], []
        for k, v in enumerate(cf['vertices']):
            cs = [int(c) for c in v['coords']]
            prev = set(seen)
            assert not (set(cs) & prev)
            seen += cs
            if v['type'] == 'D':
                assert len(cs) == 2
                dv.append((cs[0], cs[1]))
            elif v['type'] == 'W':
                assert len(cs) == 1 and int(v['ij'][0]) >= 0 and int(v['ij'][1]) >= 0
                wv.append((cs[0], int(v['ij'][0]), int(v['ij'][1])))
            elif v['type'] == 'C':
                assert len(CFGS) == 1, "C vertices only in single-configuration certificates"
                src = [int(c) for c in v['src']]
                given = [vec(g) for g in v['given']]
                assert len(src) == len(cs) >= 1 and all(c in prev for c in src), "src: earlier coordinates"
                assert all(g[c] == 0 for g in given for c in range(NC) if c not in prev), "given: earlier coordinates"
                cv.append((cs, src, given))
                CVd[k] = (cs, src, given)
            else:
                raise ValueError("unknown vertex type")
        assert sorted(seen) == list(range(NC)), "vertices must partition the coordinates"
        DVs.append(dv); WVs.append(wv); VCs.append([sorted(int(c) for c in v['coords']) for v in cf['vertices']])
        CV[:] = cv
    assert all(dv == DVs[0] for dv in DVs), "configurations must share their D vertices"
    DV[:] = DVs[0]
    WV[:] = WVs[0]

    VALUED = {}

    def setcfg(cp):
        k = cp // 2
        assert 0 <= k < len(CFGS)
        WV[:] = WVs[k]
        if k not in VALUED:
            VALUED[k] = valued_forms()
        return cp % 2, xvalued(), yvalued(), {w for w, a, b in WV}, VCs[k]
    r, XS, YS, WS, vcoords = setcfg(0)
    acc = Acc()
    counts = {}
    for row in C['rows']:
        t = row['type']
        m = Fraction(row['mult'])
        counts[t] = counts.get(t, 0) + 1
        R = Acc()
        ineq = True
        if 'copy' in row:
            r, XS, YS, WS, vcoords = setcfg(int(row['copy']))
        if t in ('sub', 'mono'):
            cp = int(row['copy'])
            K = [vec(g) for g in row['K']]
            i = vec(row['i'])
            if t == 'mono':
                R.add(Hterm(cp, K + [i]), 1)
                R.add(Hterm(cp, K), -1)
            else:
                j = vec(row['j'])
                R.add(Hterm(cp, K + [i]), 1)
                R.add(Hterm(cp, K + [j]), 1)
                R.add(Hterm(cp, K + [i, j]), -1)
                R.add(Hterm(cp, K), -1)
        elif t == 'ci':
            cp = int(row['copy'])
            ineq = False
            new = sorted(int(c) for c in row['new'])
            old = sorted(int(c) for c in row['old'])
            k = vcoords.index(new)                      # new = coordinates of one vertex
            assert VT[k] in ('D', 'W'), "ci rows only for independent (D, W) vertices"
            assert old == sorted(c for vc in vcoords[:k] for c in vc), "old must be all earlier vertices"
            R.add(Hterm(cp, [unitv(c) for c in old + new]), 1)
            R.add(Hterm(cp, [unitv(c) for c in old]), -1)
            R.add(Hterm(cp, [unitv(c) for c in new]), -1)
        elif t == 'merge':
            cp = int(row['copy'])
            ineq = False
            perm = {c: c for c in range(NC)}
            perm.update({int(a): int(b) for a, b in row['perm']})
            assert sorted(perm.values()) == list(range(NC))
            for (x, y) in DV:
                assert (perm[x], perm[y]) in DV, "perm must map D vertices to D vertices"
            wlaw = {w: (a, b) for (w, a, b) in WV}
            for w in WS:
                assert perm[w] in wlaw and wlaw[perm[w]] == wlaw[w], "perm must map W vertices to W vertices of the same law"
            G = [vec(g) for g in row['G']]
            for c in ccoords():
                assert perm[c] == c and all(g[c] == 0 for g in G), "merge rows may not involve C coordinates"
            tG = []
            for g in G:
                h = [Fraction(0)] * NC
                for c in range(NC):
                    h[perm[c]] += g[c]
                tG.append(h)
            R.add(Hterm(cp, G), -1)
            R.add(Hterm(cp, tG), 1)
        elif t == 'pmerge':
            cp = int(row['copy'])
            ineq = False
            perm = {c: c for c in range(NC)}
            perm.update({int(a): int(b) for a, b in row['perm']})
            assert sorted(perm.values()) == list(range(NC))
            G = [vec(g) for g in row['G']]
            sup = {c for g in G for c in range(NC) if g[c] != 0}
            cc_ = ccoords()
            assert not (sup & cc_) and all(perm[c] == c for c in cc_), "pmerge: G must avoid C coordinates" 
            vert_of = {}
            for k, (x, y) in enumerate(DV):
                vert_of[x] = (('D', k), 'x'); vert_of[y] = (('D', k), 'y')
            for (w, a, b) in WV:
                vert_of[w] = (('W', w), (a, b))

            def law(cc):
                vid, role = vert_of[cc]
                return ((1, 0) if role == 'x' else (0, 1)) if vid[0] == 'D' else role
            touched = {}
            for c in sup:
                touched.setdefault(vert_of[c][0], []).append(c)
            targets = set()
            for vid, cs in touched.items():
                tv = {vert_of[perm[c]][0] for c in cs}
                assert len(tv) == 1, "the touched part of a vertex must map into one vertex"
                tvid = tv.pop()
                assert tvid not in targets, "distinct vertices must map to distinct vertices"
                targets.add(tvid)
                if vid[0] == 'D' and len(cs) == 2:
                    assert tvid[0] == 'D' and all(vert_of[perm[c]][1] == vert_of[c][1] for c in cs), "D pair to D pair"
                else:
                    assert len(cs) == 1 and law(perm[cs[0]]) == law(cs[0]), "marginal laws must agree"
            tG = []
            for g in G:
                h = [Fraction(0)] * NC
                for c in range(NC):
                    h[perm[c]] += g[c]
                tG.append(h)
            R.add(Hterm(cp, G), -1)
            R.add(Hterm(cp, tG), 1)
        elif t == 'cci':
            cp = int(row['copy'])
            ineq = False
            k = int(row['vertex'])
            assert VT[k] == 'C'
            cs, src, given = CVd[k]
            old = sorted(c for vc in vcoords[:k] for c in vc)
            R.add(Hterm(cp, [unitv(c) for c in old + sorted(cs)]), 1)
            R.add(Hterm(cp, given), 1)
            R.add(Hterm(cp, [unitv(c) for c in old]), -1)
            R.add(Hterm(cp, given + [unitv(c) for c in sorted(cs)]), -1)
        elif t == 'cmerge':
            cp = int(row['copy'])
            ineq = False
            k = int(row['vertex'])
            assert VT[k] == 'C'
            cs, src, given = CVd[k]
            # later independent vertices (D, W after vertex k) are independent of (earlier coordinates, c), so
            # (c, V, later) has the law of (s, V, later): their coordinates may appear in G unchanged
            later = [unitv(c) for k2, vc in enumerate(vcoords) if k2 > k and VT[k2] in ('D', 'W') for c in vc]
            grows = rref(given + later)
            G = [vec(g) for g in row['G']]
            pG = []
            for g in G:
                rest = list(g)
                img = [Fraction(0)] * NC
                for c, s_ in zip(cs, src):
                    img[s_] += g[c]
                    rest[c] = Fraction(0)
                assert in_span(grows, rest), "cmerge generator not in span(copied coordinates, given forms)"
                pG.append([a + b for a, b in zip(rest, img)])
            R.add(Hterm(cp, pG), 1)
            R.add(Hterm(cp, G), -1)
        elif t in ('bsum', 'bdiff', 'batom'):
            cp = int(row['copy'])
            f = vec(row['f'])
            XA, YA, SP, DF = VALUED[cp // 2]
            if t == 'bsum':
                assert xy_pair(f, +1) or in_pm(f, SP), f
                R.add(('S',), 1)
            elif t == 'bdiff':
                assert xy_pair(f, -1) or in_pm(f, DF), f
                R.add(('L',), 1)
            else:
                assert (is_atom(f) and any(f[c] != 0 for c in XS | YS)) or in_pm(f, XA + YA), f
                R.add(('S',), 1)
            R.add(Hterm(cp, [f]), -1)
        elif t == 'dpair':
            cp = int(row['copy'])
            ineq = False
            x, y = DV[int(row['vertex'])]
            R.add(('L',), 1)
            R.add(Hterm(cp, [unitv(x), unitv(y)]), -1)
        elif t == 'ident':
            cp = int(row['copy'])
            ineq = False
            f = vec(row['f'])
            ij = grid_form(f)
            assert ij is not None and list(ij) == row['ij'], (f, row['ij'])
            i, j = ij if r == 0 else (ij[1], ij[0])
            assert 0 <= i <= M and 0 <= j <= M
            R.add(('h', i, j), 1)
            R.add(Hterm(cp, [f]), -1)
        elif t.startswith('g_'):
            ij = row['ij']
            h = lambda a, b: ('h', a, b) if 0 <= a <= M and 0 <= b <= M else None

            def need(*terms):
                assert all(x is not None for x in terms), (t, ij)
            if t == 'g_h00':
                ineq = False
                R.add(('h', 0, 0), -1)
            elif t == 'g_h11':
                R.add(('S',), 1)
                R.add(('h', 1, 1), -1)
            else:
                i, j = ij
                if t == 'g_nonneg':
                    need(h(i, j)); R.add(h(i, j), 1)
                elif t == 'g_monox':
                    need(h(i + 1, j), h(i, j)); R.add(h(i + 1, j), 1); R.add(h(i, j), -1)
                elif t == 'g_monoy':
                    need(h(i, j + 1), h(i, j)); R.add(h(i, j + 1), 1); R.add(h(i, j), -1)
                elif t == 'g_concx':
                    need(h(i + 2, j)); R.add(h(i + 1, j), 2); R.add(h(i, j), -1); R.add(h(i + 2, j), -1)
                elif t == 'g_concy':
                    need(h(i, j + 2)); R.add(h(i, j + 1), 2); R.add(h(i, j), -1); R.add(h(i, j + 2), -1)
                elif t == 'g_link':
                    need(h(i + 1, j), h(i, j + 1))
                    R.add(h(i + 1, j), 1); R.add(h(i, j + 1), 1); R.add(h(i, j), -1); R.add(('L',), -1)
                else:
                    raise ValueError(t)
        elif t == 'share':
            ineq = False
            cpy = int(row['copy'])
            G = [vec(g) for g in row['G']]
            dco = {c for pr in DV for c in pr}
            for g in G:
                assert all(g[c] == 0 for c in range(NC) if c not in dco), "share generators must be D-only"
            pG = []
            for g in G:
                h = list(g)
                if r == 1:
                    for (x, y) in DV:
                        h[x], h[y] = -g[y], -g[x]
                pG.append(h)
            R.add(Hterm(0, pG), 1)
            R.add(Hterm(cpy, G), -1)
        elif t == 'xshare':
            ineq = False
            r, XS, YS, WS, vcoords = setcfg(0)          # copies 0 and 1 of configuration 0
            G = [vec(g) for g in row['G']]
            mp = {int(a): int(b) for a, b in row['map']}
            sup = {c for g in G for c in range(NC) if g[c] != 0}
            assert set(mp) == sup, "map must be defined exactly on the support"
            cc_ = ccoords()
            assert not (sup & cc_) and not (set(mp.values()) & cc_), "xshare: no C coordinates"
            vert_of = {}
            for k, (x, y) in enumerate(DV):
                vert_of[x] = (('D', k), 'x'); vert_of[y] = (('D', k), 'y')
            wlaw = {w: (a, b) for (w, a, b) in WV}
            for w in wlaw:
                vert_of[w] = (('W', w), wlaw[w])
            touched = {}
            for c in sup:
                touched.setdefault(vert_of[c][0], []).append(c)
            targets = set()
            for vid, cs in touched.items():
                tv = {vert_of[mp[c]][0] for c in cs}
                assert len(tv) == 1, "the touched part of a vertex must map into one vertex"
                tvid = tv.pop()
                assert tvid not in targets, "distinct vertices must map to distinct vertices"
                targets.add(tvid)
                if vid[0] == 'D' and len(cs) == 2:
                    x, y = DV[vid[1]]
                    assert tvid[0] == 'D' and vert_of[mp[x]][1] == 'y' and vert_of[mp[y]][1] == 'x', "pair -> (-y, -x)"
                else:
                    assert len(cs) == 1
                    c = cs[0]; i = mp[c]
                    src_law = ((1, 0) if vert_of[c][1] == 'x' else (0, 1)) if vid[0] == 'D' else vert_of[c][1]
                    tgt_law = ((1, 0) if vert_of[i][1] == 'x' else (0, 1)) if tvid[0] == 'D' else vert_of[i][1]
                    assert tgt_law == (src_law[1], src_law[0]), "laws must be transposed (mu' <-> nu, nu' <-> mu)"
            pG = []
            for g in G:
                h = [Fraction(0)] * NC
                for c in sup:
                    h[mp[c]] -= g[c]
                pG.append(h)
            R.add(Hterm(0, pG), 1)
            R.add(Hterm(1, G), -1)
        elif t == 'rshare':
            ineq = False
            r, XS, YS, WS, vcoords = setcfg(0)          # copies 0 and 1 of configuration 0
            G = [vec(g) for g in row['G']]
            wm = {int(a): int(b) for a, b in row.get('wmap', [])}
            wlaw = {w: (a, b) for (w, a, b) in WV}
            assert len(set(wm.values())) == len(wm), "wmap must be injective"
            for a, b in wm.items():
                assert a in wlaw and b in wlaw and wlaw[b] == (wlaw[a][1], wlaw[a][0]), "wmap: W -> W, transposed law"
            dco = {c for pr in DV for c in pr}
            for g in G:
                assert all(g[c] == 0 for c in range(NC) if c not in dco and c not in wm), \
                    "rshare generators must be supported on D coordinates and wmap'd W coordinates"
            pG = []
            for g in G:
                h = [Fraction(0)] * NC
                for (x, y) in DV:
                    h[x], h[y] = -g[y], -g[x]
                for a, b in wm.items():
                    h[b] -= g[a]
                pG.append(h)
            R.add(Hterm(0, pG), 1)
            R.add(Hterm(1, G), -1)
        elif t.startswith('sg_'):
            def sgk(tt):
                tt = tuple(int(x) for x in tt)
                assert len(tt) == 4 and all(x >= 0 for x in tt), tt
                return ('sg', min(tt, (tt[1], tt[0], tt[3], tt[2])))
            add4 = lambda tt, dd, m=1: tuple(int(x) + m * int(y) for x, y in zip(tt, dd))
            units = [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]
            if t == 'sg_h':
                ineq = False
                a, b = int(row['ab'][0]), int(row['ab'][1])
                assert 0 <= a <= M and 0 <= b <= M
                R.add(('h', a, b), 1); R.add(sgk((a, 0, b, 0)), -1)
            elif t == 'sg_nonneg':
                R.add(sgk(row['t']), 1)
            elif t in ('sg_mono', 'sg_conc'):
                d = tuple(int(x) for x in row['d'])
                assert d in units
                if t == 'sg_mono':
                    R.add(sgk(add4(row['t'], d)), 1); R.add(sgk(row['t']), -1)
                else:
                    R.add(sgk(add4(row['t'], d)), 2); R.add(sgk(row['t']), -1); R.add(sgk(add4(row['t'], d, 2)), -1)
            elif t == 'sg_link':
                dx = tuple(int(x) for x in row['dx'])
                assert dx in ((1, 0, 0, 0), (0, 1, 0, 0))
                dy = (0, 0, 1, 0) if dx == (1, 0, 0, 0) else (0, 0, 0, 1)
                R.add(sgk(add4(row['t'], dx)), 1); R.add(sgk(add4(row['t'], dy)), 1)
                R.add(sgk(row['t']), -1); R.add(('L',), -1)
            elif t == 'sg_diff':
                R.add(('L',), 1); R.add(sgk((1, 0, 0, 1)), -1)
            elif t == 'sg_ident':
                ineq = False
                cp = int(row['copy'])
                f = vec(row['f'])
                assert all(a in (-1, 0, 1) for a in f) and all(f[c] == 0 for c in ccoords()), f
                n = [0, 0, 0, 0]
                used = set()
                for (x, y) in DV:
                    assert not (f[x] != 0 and f[y] != 0), "at most one coordinate per D vertex"
                    n[0] += int(f[x] == 1); n[1] += int(f[x] == -1); n[2] += int(f[y] == 1); n[3] += int(f[y] == -1)
                    used |= {x, y}
                for (w, wi, wj) in WV:
                    used.add(w)
                    if f[w] == 1:
                        n[0] += wi; n[2] += wj
                    elif f[w] == -1:
                        n[1] += wi; n[3] += wj
                assert all(f[c] == 0 for c in range(NC) if c not in used)
                tt = tuple(n) if r == 0 else (n[3], n[2], n[1], n[0])
                assert sum(tt) > 0
                R.add(sgk(tt), 1)
                R.add(Hterm(cp, [f]), -1)
            else:
                raise ValueError(t)
        elif t.startswith('mg_') or t == 'mgident':
            cp = int(row['copy'])
            fam = tuple(int(x) for x in row['fam'])
            assert fam in ((1, 1), (1, -1)), fam
            i, j = int(row['ij'][0]), int(row['ij'][1])
            inb = lambda a, b: 0 <= a <= M and 0 <= b <= M
            g = lambda a, b: ('g', cp, fam, a, b) if inb(a, b) else None
            hc = lambda a, b: (('h', a, b) if r == 0 else ('h', b, a)) if inb(a, b) else None

            def need(*terms):
                assert all(x is not None for x in terms), (t, row['ij'])
            if t == 'mg_nonneg':
                need(g(i, j)); R.add(g(i, j), 1)
            elif t == 'mg_monox':
                need(g(i + 1, j), g(i, j)); R.add(g(i + 1, j), 1); R.add(g(i, j), -1)
            elif t == 'mg_monoy':
                need(g(i, j + 1), g(i, j)); R.add(g(i, j + 1), 1); R.add(g(i, j), -1)
            elif t == 'mg_concx':
                need(g(i + 2, j)); R.add(g(i + 1, j), 2); R.add(g(i, j), -1); R.add(g(i + 2, j), -1)
            elif t == 'mg_concy':
                need(g(i, j + 2)); R.add(g(i, j + 1), 2); R.add(g(i, j), -1); R.add(g(i, j + 2), -1)
            elif t == 'mg_geh':
                need(g(i, j), hc(i, j)); R.add(g(i, j), 1); R.add(hc(i, j), -1)
            elif t == 'mg_le1':
                need(g(i, j), hc(i + 1, j)); R.add(hc(i + 1, j), 1); R.add(hc(0, 1), 1); R.add(g(i, j), -1)
            elif t == 'mg_ge1':
                need(g(i, j), hc(i + 1, j)); R.add(g(i, j), 1); R.add(hc(0, 1), 1); R.add(hc(i + 1, j), -1)
            elif t == 'mg_le2':
                assert fam == (1, 1)
                need(g(i, j), hc(i, j + 1)); R.add(hc(i, j + 1), 1); R.add(hc(1, 0), 1); R.add(g(i, j), -1)
            elif t == 'mg_ge2':
                assert fam == (1, 1)
                need(g(i, j), hc(i, j + 1)); R.add(g(i, j), 1); R.add(hc(1, 0), 1); R.add(hc(i, j + 1), -1)
            elif t == 'mgident':
                ineq = False
                f = vec(row['f'])
                assert all(f[c] == 0 for c in ccoords()), "mgident forms may not involve C coordinates"
                # exactly one D vertex carries (a, b); the others carry 0/1 on at most one coordinate; W's 0/1
                base = [k for k, (x, y) in enumerate(DV) if (f[x], f[y]) == (fam[0], fam[1])]
                assert len(base) >= 1, f
                ok = False
                for kb in base:
                    gi = gj = 0
                    good = True
                    for k, (x, y) in enumerate(DV):
                        if k == kb:
                            continue
                        if (f[x], f[y]) == (0, 0):
                            continue
                        if (f[x], f[y]) == (1, 0):
                            gi += 1
                        elif (f[x], f[y]) == (0, 1):
                            gj += 1
                        else:
                            good = False
                    for (w, wi, wj) in WV:
                        if f[w] == 1:
                            gi += wi; gj += wj
                        elif f[w] != 0:
                            good = False
                    if good and (gi, gj) == (i, j):
                        ok = True
                        break
                assert ok, (f, row['ij'])
                need(g(i, j))
                R.add(g(i, j), 1)
                R.add(Hterm(cp, [f]), -1)
            else:
                raise ValueError(t)
        elif t in ('matus4', 'five'):
            cp = int(row['copy'])
            V = [[vec(g) for g in gl] for gl in row['vars']]

            def Hj(*idx):
                gens = []
                for k in idx:
                    gens += V[k]
                return Hterm(cp, gens)

            def I(w, p, q, r=None):
                if r is None:
                    R.add(Hj(p), w); R.add(Hj(q), w); R.add(Hj(p, q), -w)
                else:
                    R.add(Hj(p, r), w); R.add(Hj(q, r), w); R.add(Hj(p, q, r), -w); R.add(Hj(r), -w)
            a, b, c, d = 0, 1, 2, 3

            def ingleton(w, x, y, z, u):
                I(-w, x, y); I(w, x, y, z); I(w, x, y, u); I(w, z, u)
            if t == 'matus4':
                s = int(row['s'])
                assert s >= 1
                I(1, b, c, a)
                ingleton(s, a, b, c, d)
                I(s * (s + 1) // 2, a, c, b)
                I(s * (s + 1) // 2, a, b, c)
            else:
                z = 4
                k = int(row['k'])
                assert k >= 1 and row['fam'] in ('M', 'C') and row['variant'] in ('abcd', 'acbd')
                if row['variant'] == 'abcd':
                    ingleton(k, a, b, c, d)
                else:
                    ingleton(k, a, c, b, d)
                kk = k * (k - 1) // 2
                if row['fam'] == 'M':
                    I(1, b, z, a); I(k, a, z, b); I(k, a, b, z); I(kk, a, c, b); I(kk, a, b, c)
                else:
                    I(1, a, b, z); I(k, a, z, b); I(k, b, z, a); I(kk, a, c, b); I(kk, b, c, a)
        else:
            raise ValueError("unknown row type " + t)
        if ineq and m < 0:
            raise AssertionError(f"negative multiplier on inequality row {t}")
        for term, cf in R.t.items():
            acc.add(term, m * cf)
    target = {('S',): lam, ('L',): Fraction(-1)}
    resid = {k: v for k, v in acc.t.items() if v != target.get(k, 0)}
    for k in target:
        if k not in acc.t and target[k] != 0:
            resid[k] = Fraction(0)
    if resid:
        print("FAIL: identity does not hold; residual terms:", len(resid))
        for k, v in list(resid.items())[:10]:
            print("  ", k[:2], v, "target", target.get(k, 0))
        return False
    print(f"PASS: L <= lambda * S with lambda = {lam} = {float(lam):.12f}")
    print("row counts:", dict(sorted(counts.items())))
    return True


if __name__ == '__main__':
    ok = check(sys.argv[1])
    sys.exit(0 if ok else 1)
