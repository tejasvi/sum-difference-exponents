#!/usr/bin/env python3
"""Audit checker for the certificates read by checker/check630.py (indep_check2: + lemma rows verified by my own lemma_verify.py), written without reading the search code's internals and
using a different code path from check630.py.

Usage: python -I indep_check.py CERT.json [--no-inj] [--print-config]

Mathematical content (my own reading of the copy lemma; nothing imported from the search programs or from checker/check630.py):
  * Vertex v carries coordinates (x_v, y_v), each vertex distributed as (X, Y).  The configuration is kept as
    an explicit PARAMETRIZATION: x_v, y_v are vectors in Q^k (coefficients of k abstract parameters).  The
    linear relations known to hold a.s. are exactly the kernel of the map
        (formal combination of coordinates) -> (vector in Q^k).
  * Copy step (U, V): W = span of cl(V) (closure in the current configuration).  The relations transferred
    to the copies U' are alpha(U') = alpha(U) for every combination alpha of U-coordinates whose vector lies
    in W.  Implementation: A = {alpha : sum alpha_i M_i in W} (M_i = vectors of U-coordinates); A^perp =
    column space of N, N[i][j] = M_i . z_j with z_j a basis of W^perp; new coordinates
    U' = U + delta, delta_i = sum_j c_j[i] * e_{k+j} with c_j a basis of A^perp (fresh parameters).
    Then alpha(U') - alpha(U) = (alpha . c_j)_j e_new vanishes iff alpha in A.
  * Closure of a set S of forms: the subspace W = span(S), enlarged by (x_v, y_v) whenever x_v - y_v in W,
    until stable.  A flat is identified by the canonical RREF of W.  (--no-inj disables the injectivity
    rule, as a negative control.)
  * Rows: sub I(i;j|K) >= 0, mono H(K,i) - H(K) >= 0 (multipliers must be >= 0), ci (step t)
    H(V,U') + H(old) - H(old,U') - H(V) = 0 (any sign), eqlaw merges H(cl(gens)) = H(cl(tau gens)).
  * Identity: H(g0) + sum mult*row - sum_r lambda_r H(pi_r(g0)) must vanish on every connected component of
    the merge graph (components found by BFS, not union-find).
  * Non-Shannon rows "matus" (added for nsc116*): for joint variables a, b, c, d (lists of forms) and an integer s
    with 1 <= s <= MATUS_SMAX, Matus' inequality in the form of Dougherty-Freiling-Zeger (arXiv:1104.3602,
    eq. (80) = Matus 2007, Cor. 3, formula (4)):
        s I(a;b) <= s(s+3)/2 I(a;b|c) + s(s+1)/2 I(a;c|b) + I(b;c|a) + s I(a;b|d) + s I(c;d).
    Validity for every s <= MATUS_SMAX is proved independently by matus_lp.py / matus_param.py (induction via a
    copy of a over bc; the closed-form step identity is a degree-2 polynomial identity in s, so it holds for all s).
    Multipliers must be >= 0.
"""
import json
import sys
from fractions import Fraction
from collections import defaultdict, deque

import flint

D = (1, -1)
MATUS_SMAX = 1000  # range verified exactly: matus_lp.py (s <= 30, LP) and matus_param.py (closed form, s <= 1000)


def fq(x):
    return flint.fmpq(x.numerator, x.denominator) if isinstance(x, Fraction) else flint.fmpq(int(x))


def to_frac(q):
    return Fraction(int(q.p), int(q.q))


def rref_basis(vectors, k):
    """Canonical RREF basis (tuple of tuples of Fractions) of the span of vectors in Q^k."""
    vecs = [v for v in vectors if any(a != 0 for a in v)]
    if not vecs:
        return ()
    M = flint.fmpq_mat(len(vecs), k, [fq(a) for v in vecs for a in v])
    R, r = M.rref()
    return tuple(tuple(to_frac(R[i, j]) for j in range(k)) for i in range(r))


def in_span(basis, v, k):
    if not any(a != 0 for a in v):
        return True
    if not basis:
        return False
    return len(rref_basis(list(basis) + [v], k)) == len(basis)


def nullspace_rows(basis, k):
    """Basis of {z in Q^k : b . z = 0 for all b in basis}."""
    R = rref_basis(list(basis), k)
    piv = [next(j for j in range(k) if row[j] != 0) for row in R]
    out = []
    for f in range(k):
        if f in piv:
            continue
        z = [Fraction(0)] * k
        z[f] = Fraction(1)
        for row, p in zip(R, piv):
            z[p] = -row[f]
        out.append(z)
    for b in basis:
        for z in out:
            assert sum(x * y for x, y in zip(b, z)) == 0
    return out


class Param:
    def __init__(self, slopes, inj=True):
        self.R = [tuple(s) for s in slopes]
        self.SL = self.R + [D]
        self.k = 2
        self.vx = [[Fraction(1), Fraction(0)]]
        self.vy = [[Fraction(0), Fraction(1)]]
        self.steps = []
        self.inj = inj

    @property
    def n(self):
        return len(self.vx)

    def form(self, v, s):
        a, b = s
        return [a * p + b * q for p, q in zip(self.vx[v], self.vy[v])]

    def amb(self, f):
        """Ambient integer vector f (length <= 2n; coordinates x_0, y_0, x_1, ...) -> parameter vector."""
        out = [Fraction(0)] * self.k
        for idx, c in enumerate(f):
            if c == 0:
                continue
            v, comp = divmod(idx, 2)
            src = self.vx[v] if comp == 0 else self.vy[v]
            out = [o + c * s for o, s in zip(out, src)]
        return out

    def closure(self, vecs, nverts=None):
        if nverts is None:
            nverts = self.n
        W = rref_basis(vecs, self.k)
        while True:
            grew = False
            if self.inj:
                for v in range(nverts):
                    d = [p - q for p, q in zip(self.vx[v], self.vy[v])]
                    if in_span(W, d, self.k):
                        for w in (self.vx[v], self.vy[v]):
                            if not in_span(W, w, self.k):
                                W = rref_basis(list(W) + [w], self.k)
                                grew = True
            if not grew:
                return W

    def _extend(self, extra):
        z = [Fraction(0)] * extra
        self.vx = [v + z for v in self.vx]
        self.vy = [v + z for v in self.vy]
        self.k += extra

    def copy_step(self, U, V):
        for v, s in V:
            assert 0 <= v < self.n and tuple(s) in self.SL, (v, s)
        assert len(set(U)) == len(U) and all(0 <= u < self.n for u in U)
        W = self.closure([self.form(v, tuple(s)) for v, s in V])
        Z = nullspace_rows(W, self.k)                      # W^perp
        M = []
        for u in U:
            M.append(self.vx[u])
            M.append(self.vy[u])
        N = [[sum(a * b for a, b in zip(Mi, z)) for z in Z] for Mi in M]   # 2|U| x dim W^perp
        # column space of N, as vectors in Q^{2|U|}
        cols = [[N[i][j] for i in range(len(M))] for j in range(len(Z))]
        C = rref_basis(cols, len(M)) if cols else ()
        f = len(C)
        k0 = self.k
        self._extend(f)
        M = [Mi + [Fraction(0)] * f for Mi in M]
        newids = []
        for t, u in enumerate(U):
            for comp in (0, 1):
                i = 2 * t + comp
                vec = list(M[i])
                for j, c in enumerate(C):
                    vec[k0 + j] += c[i]
                if comp == 0:
                    self.vx.append(vec)
                else:
                    self.vy.append(vec)
            newids.append(self.n - 1)
        self.steps.append(('copy', list(U), [(int(v), tuple(s)) for v, s in V], newids))
        return newids


def build(C, inj=True):
    P = Param(C['slopes'], inj=inj)
    for st in C['steps']:
        if 'link' in st:
            raise SystemExit("FAIL: link steps not supported by this audit checker")
        P.copy_step(list(st['U']), [(v, tuple(s)) for v, s in st['V']])
    return P


def ref_vec(P, x, extra):
    if x[0] == 'amb':
        return P.amb(extra[int(x[1])])
    v, s = int(x[0]), (int(x[1][0]), int(x[1][1]))
    if not (0 <= v < P.n and s in P.SL):
        raise SystemExit(f"FAIL: bad form reference {x}")
    return P.form(v, s)


def check(C, inj=True, verbose=True, print_config=False):
    P = build(C, inj=inj)
    extra = [list(map(int, f)) for f in C.get('extra', [])]
    for f in C.get('extra', []):
        if any(int(a) != a for a in f):
            raise SystemExit("FAIL: non-integer extra form")
        if len(f) != 2 * P.n:
            raise SystemExit("FAIL: extra form has wrong length")
    if verbose:
        print(f"[audit] configuration: {P.n} vertices, {P.k} free parameters, {len(extra)} extra forms")
    if print_config:
        for v in range(P.n):
            print(f"   g{v}: x = {[str(a) for a in P.vx[v]]}, y = {[str(a) for a in P.vy[v]]}")
    cache = {}

    def H(vecs):
        key = tuple(tuple(v) for v in vecs)
        if key not in cache:
            cache[key] = P.closure(vecs)
        return cache[key]

    resid = defaultdict(Fraction)
    LEM = None
    if C.get('lemmas'):
        import os as _os
        sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))
        import lemma_verify
        try:
            LEM = lemma_verify.verify_all(C['lemmas'])
        except lemma_verify.LemmaError as e:
            return False, f'lemma verification failed: {e}'

    def add(flat, c):
        if flat == ():
            return
        resid[flat] += c

    for r in C['rows']:
        m = Fraction(r['mult'])
        t = r['type']
        if t in ('sub', 'mono'):
            if m < 0:
                return False, "negative multiplier on a Shannon row"
            K = [ref_vec(P, g, extra) for g in r['K']]
            i = ref_vec(P, r['i'], extra)
            if t == 'sub':
                j = ref_vec(P, r['j'], extra)
                add(H(K + [i]), m)
                add(H(K + [j]), m)
                add(H(K + [i, j]), -m)
                add(H(K), -m)
            else:
                add(H(K + [i]), m)
                add(H(K), -m)
        elif t == 'matus':
            if m < 0:
                return False, "negative multiplier on a matus row"
            sv = r['s']
            if not isinstance(sv, int) or not (1 <= sv <= MATUS_SMAX):
                return False, f"matus s = {sv!r} not an integer in [1, {MATUS_SMAX}]"
            a = [ref_vec(P, g, extra) for g in r['a']]
            b = [ref_vec(P, g, extra) for g in r['b']]
            c = [ref_vec(P, g, extra) for g in r['c']]
            d = [ref_vec(P, g, extra) for g in r['d']]

            def mi(x, y, z, coef):
                # coef * I(x; y | z) for joint variables x, y, z (lists of forms)
                add(H(x + z), coef)
                add(H(y + z), coef)
                add(H(x + y + z), -coef)
                add(H(z), -coef)
            S = Fraction(sv)
            # s(s+3)/2 I(a;b|c) + s(s+1)/2 I(a;c|b) + I(b;c|a) + s I(a;b|d) + s I(c;d) - s I(a;b) >= 0
            mi(a, b, c, m * S * (S + 3) / 2)
            mi(a, c, b, m * S * (S + 1) / 2)
            mi(b, c, a, m)
            mi(a, b, d, m * S)
            mi(c, d, [], m * S)
            mi(a, b, [], -m * S)
        elif t == 'lemma':
            # sum_S coef_S H(union over S of the row's argument form lists) >= 0, the lemma being verified by my own
            # lemma_verify.verify_all (copy-lemma proofs, Shannon multipliers >= 0, apply entries, acyclic)
            if m < 0:
                return False, "negative multiplier on a lemma row"
            if LEM is None:
                return False, "lemma row but no verified lemmas"
            lid = str(r['lemma'])
            if lid not in LEM:
                return False, f"lemma {lid} missing"
            lbase, lcoef = LEM[lid]
            if len(r['args']) != len(lbase):
                return False, "lemma row needs one argument per base variable"
            argv = {x: [ref_vec(P, g, extra) for g in a] for x, a in zip(lbase, r['args'])}
            for S, cS in lcoef.items():
                gens = [v for x in sorted(S) for v in argv[x]]
                add(H(gens), m * cS)
        elif t == 'ci':
            kind, U, V, newids = P.steps[int(r['step'])]
            old = [P.form(v, s) for v in range(newids[0]) for s in P.SL]
            new = [P.form(v, s) for v in newids for s in P.SL]
            Vv = [P.form(v, s) for v, s in V]
            add(H(Vv + new), m)
            add(H(old), m)
            add(H(old + new), -m)
            add(H(Vv), -m)
        else:
            return False, f"unknown row type {t}"
    add(H([P.form(0, (1, 0)), P.form(0, (0, 1))]), Fraction(1))
    lam = {}
    for key, val in C['lambda'].items():
        a, b = (int(x) for x in key.split(','))
        lam[(a, b)] = Fraction(val)
        if lam[(a, b)] < 0:
            return False, "negative lambda"
        if (a, b) not in P.R:
            return False, "lambda on slope outside R"
    for s, val in lam.items():
        add(H([P.form(0, s)]), -val)
    # merge graph
    adj = defaultdict(set)
    for e in C['eqlaw']:
        kind, U, V, newids = P.steps[int(e['step'])]
        gens, img = [], []
        for g in e['gens']:
            if g[0] == 'amb':
                return False, "eqlaw generator is an extra form"
            v, s = int(g[0]), (int(g[1][0]), int(g[1][1]))
            if (v, s) in V:
                img.append(P.form(v, s))
            elif v in U:
                img.append(P.form(newids[U.index(v)], s))
            else:
                return False, f"eqlaw generator {g} not a U-form or V-form of step {e['step']}"
            gens.append(P.form(v, s))
        if not gens:
            return False, "empty eqlaw"
        F, G = H(gens), H(img)
        adj[F].add(G)
        adj[G].add(F)
    seen = set()
    nodes = set(resid) | set(adj)
    bad = []
    for start in nodes:
        if start in seen:
            continue
        comp, dq = [], deque([start])
        seen.add(start)
        while dq:
            a = dq.popleft()
            comp.append(a)
            for b in adj[a]:
                if b not in seen:
                    seen.add(b)
                    dq.append(b)
        tot = sum((resid.get(a, Fraction(0)) for a in comp), Fraction(0))
        if tot != 0:
            bad.append((len(comp), tot))
    if bad:
        return False, f"identity fails on {len(bad)} merge components, e.g. {bad[:3]}"
    Ctot = sum(lam.values())
    if 'claimed_C' in C and Fraction(C['claimed_C']) != Ctot:
        return False, f"claimed_C {C['claimed_C']} != sum lambda {Ctot}"
    return True, Ctot


if __name__ == '__main__':
    args = sys.argv[1:]
    path = [a for a in args if not a.startswith('--')][0]
    C = json.load(open(path))
    ok, info = check(C, inj='--no-inj' not in args, print_config='--print-config' in args)
    if ok:
        lam = {k: str(v) for k, v in C['lambda'].items()}
        print(f"[audit] PASS: H(X,Y) <= sum lambda_r H(pi_r), lambda = {lam}; C = {info} = {float(info):.12f}")
        sys.exit(0)
    print(f"[audit] FAIL: {info}")
    sys.exit(1)
