#!/usr/bin/env python3
"""Independent exact checker for entropy certificates of sum-difference bounds.

Usage: python3 check630.py CERT.json

Claim checked: for every pair (X, Y) of integer-valued, finitely supported random variables such that
X - Y is injective on the support of (X, Y),
        H(X, Y) <= sum_r lambda_r H(a_r X + b_r Y),      r = (a_r, b_r) ranging over the slopes R.

Definitions (shared with the search code only through this documentation):
  * A configuration has vertices g_0..g_{n-1} (coordinates x_v, y_v), each distributed as (X, Y), and a
    space Rel of ambient linear relations (vectors in Q^{2n}) that hold almost surely.
  * Standard form pi_s(v) = a x_v + b y_v for s = (a, b) in R + [(1, -1)].  Extra forms: integer vectors
    in Z^{2n} listed in the certificate (linear functions of the final configuration).
  * Copy step {U, V} (copy lemma): new vertices U' = copies of U with (U', V) equal in law to (U, V) and
    U' conditionally independent of all existing vertices given V.  New relations: tau(alpha) - alpha = 0
    for every alpha supported on the coordinates of U with alpha in span(cl(V)) + Rel; tau moves the
    coordinates of u in U to those of its copy u'.
  * Link step {link: [U, u, w, l]}: new vertices U' = copies of U (U' equal in law to U), conditionally
    independent of all existing vertices given the linked forms of w; relations: tau(alpha) = 0 for every
    alpha supported on U coordinates with alpha in Rel (inherited), and pi_l(u') = pi_l(w) (l a slope) or
    u' = w (l = "id").  Valid because pi_l(u) and pi_l(w) (resp. u and w) have the same law.
  * cl(S) (computed in the configuration at hand, ground set = its standard forms, plus the extra forms
    for the final configuration): smallest set containing S, closed under (i) linear span modulo Rel and
    (ii) if pi_(1,-1)(v) is in the set then so are pi_(1,0)(v), pi_(0,1)(v).  Sound: H(cl S) = H(S).
  * Rows: "sub" I(i; j | K) >= 0, "mono" H(K u {i}) - H(K) >= 0 (Shannon); "ci" (step t):
    H(cl(V u U')) + H(cl(old)) - H(cl(old u U')) - H(cl(V)) = 0; "eqlaw" (step t): copy step: gens in
    forms(U) u V, H(cl(gens)) = H(cl(tau gens)) with tau fixing V; link step: gens in forms(U).
  * "matus" rows (s, a, b, c, d; each of a, b, c, d a set of forms viewed as one joint variable):
    M_s(a,b,c,d) = I(b;c|a) + s*(-I(a;b) + I(a;b|c) + I(a;b|d) + I(c;d)) + s(s+1)/2*(I(a;c|b) + I(a;b|c))
    >= 0 for s >= 1: Matus' four-variable family (F. Matus, "Infinitely many information inequalities",
    ISIT 2007), written with the roles of a and b exchanged relative to Matus' statement
    s[I(A;B|C)+I(A;B|D)+I(C;D)-I(A;B)] + I(A;C|B) + s(s+1)/2 [I(B;C|A)+I(A;B|C)] >= 0; s = 1 is a form of the
    Zhang-Yeung inequality.  Multipliers must be >= 0.
  * "lemma" rows (lemma id, args = one set of forms per base variable, each set viewed as one joint variable):
    sum_S coef_S H(union of args over S) >= 0, where the lemma (certificate field "lemmas") states a linear
    inequality sum_S coef_S H(S) >= 0 over the nonempty subsets S of its base variables and is verified here
    from its proof: auxiliary variables are introduced by copy steps {new, src, over} (one new variable per src
    item; an item is a group of existing variables taken jointly).  Copy lemma: for discrete random variables
    there are new variables with (new, over) equal in law to (src, over) and new conditionally independent of
    all existing variables given over (take p(old) * p_{src|over}(new | over)).  Hence (eqlaw) H(S) = H(phi(S))
    for S in new u over meeting new, phi replacing each new variable by its src group, and (ci)
    H(new u over) + H(old) - H(new u old) - H(over) = 0.  The proof lists multipliers on elemental Shannon
    inequalities ("mono": H(all) - H(all - x); "sub": I(x;y|K)), which must be >= 0, and on eqlaw/ci equalities
    (any sign) and, optionally, nonnegative multipliers on "apply" entries: another lemma of the certificate
    (verified first; cycles rejected) with its base variables replaced by unions of variables (joint variables);
    their sum must equal coef on subsets of the base and 0 on every other subset.  The inequality then holds for
    all discrete random variables, in particular for joint variables made of forms.
  * Identity: H(g_0) + sum_rows mult * row  ==  sum_r lambda_r H(pi_r(g_0)), modulo eqlaw classes,
    with H(empty) = 0, lambda_r >= 0 and mult >= 0 on Shannon, matus and lemma rows.
This file uses only the Python standard library (fractions); it does not import the search code.
"""
import json, sys
from fractions import Fraction

D = (1, -1)


def rref(vectors):
    """Return list of (pivot, row) in reduced row echelon form (rows as lists of Fractions)."""
    rows = []
    for v in vectors:
        v = [Fraction(a) for a in v]
        for p, r in rows:
            if v[p] != 0:
                c = v[p]
                v = [a - c * b for a, b in zip(v, r)]
        piv = next((i for i, a in enumerate(v) if a != 0), None)
        if piv is None:
            continue
        c = v[piv]
        v = [a / c for a in v]
        new = []
        for p, r in rows:
            if r[piv] != 0:
                cc = r[piv]
                r = [a - cc * b for a, b in zip(r, v)]
            new.append((p, r))
        new.append((piv, v))
        rows = new
    return rows


def reduce_vec(v, rows):
    v = [Fraction(a) for a in v]
    for p, r in rows:
        if v[p] != 0:
            c = v[p]
            v = [a - c * b for a, b in zip(v, r)]
    return v


def left_null(vectors, ncols):
    """Basis of {c : sum_i c_i vectors[i] = 0}."""
    k = len(vectors)
    out, rows = [], []
    for i in range(k):
        v = [Fraction(a) for a in vectors[i]] + [Fraction(1 if j == i else 0) for j in range(k)]
        for p, r in rows:
            if v[p] != 0:
                c = v[p]
                v = [a - c * b for a, b in zip(v, r)]
        piv = next((t for t in range(ncols) if v[t] != 0), None)
        if piv is None:
            out.append(v[ncols:])
            continue
        c = v[piv]
        v = [a / c for a in v]
        rows.append((piv, v))
    return out


def sub_coord_space(Z, keep, n2):
    """Basis of vectors in span(Z) supported on the coordinate set `keep` (ambient length n2)."""
    Zb = [r for p, r in rref(Z)]
    if not Zb:
        return []
    outside = [i for i in range(n2) if i not in keep]
    M = [[r[i] for i in outside] for r in Zb]
    out = []
    for c in left_null(M, len(outside)):
        a = [sum(ci * r[i] for ci, r in zip(c, Zb)) for i in range(n2)]
        assert all(a[i] == 0 for i in outside)
        if any(a):
            out.append(a)
    return out


class Conf:
    def __init__(self, slopes):
        self.R = [tuple(s) for s in slopes]
        self.SL = self.R + [D]
        self.n = 1
        self.rel = []
        self.steps = []        # (kind, U, V, newids)
        self.extra = []        # extra forms (final configuration only)

    def pad(self, f):
        return [Fraction(a) for a in f] + [Fraction(0)] * (2 * self.n - len(f))

    def vec(self, g):
        if g[0] == 'amb':
            return self.pad(self.extra[g[1]])
        _, v, (a, b) = g
        f = [Fraction(0)] * (2 * self.n)
        f[2 * v] = Fraction(a)
        f[2 * v + 1] = Fraction(b)
        return f

    def relrows(self):
        return rref([self.pad(r) for r in self.rel])

    def nf(self, f, R):
        v = reduce_vec(self.pad(f), R)
        piv = next((i for i, a in enumerate(v) if a != 0), None)
        if piv is None:
            return None
        c = v[piv]
        return tuple(a / c for a in v)

    def ground(self):
        g = [('std', v, s) for v in range(self.n) for s in self.SL]
        g += [('amb', k) for k in range(len(self.extra))]
        return g

    def closure(self, gens, cache=None):
        key = frozenset(gens)
        if cache is not None and key in cache:
            return cache[key]
        R = self.relrows()
        nfs = {}
        for g in self.ground():
            x = self.nf(self.vec(g), R)
            if x is None:
                if g[0] == 'std':
                    raise ValueError("standard form vanishes on the configuration")
                continue
            nfs[g] = x
        cur = set(nfs[g] for g in gens)
        while True:
            rows = rref([list(x) for x in cur])
            new = set(cur)
            for g, x in nfs.items():
                if x not in new and all(a == 0 for a in reduce_vec(x, rows)):
                    new.add(x)
            for v in range(self.n):
                if nfs[('std', v, D)] in new:
                    new.add(nfs[('std', v, (1, 0))])
                    new.add(nfs[('std', v, (0, 1))])
            if new == cur:
                break
            cur = new
        res = frozenset(cur)
        if cache is not None:
            cache[key] = res
        return res

    def _add_vertices(self, U):
        n_old = self.n
        newids = list(range(n_old, n_old + len(U)))
        self.n = n_old + len(U)
        self.rel = [self.pad(r) for r in self.rel]
        return newids

    def _tau(self, alpha, U, newids, minus_old):
        r = [Fraction(0)] * (2 * self.n)
        for k, u in enumerate(U):
            up = newids[k]
            for c in (0, 1):
                if minus_old:
                    r[2 * u + c] -= alpha[2 * u + c]
                r[2 * up + c] += alpha[2 * u + c]
        return r

    def attach(self, U, V):
        V = [('std', v, tuple(s)) for v, s in V]
        for _, v, s in V:
            assert 0 <= v < self.n and s in self.SL
        assert len(set(U)) == len(U) and all(0 <= u < self.n for u in U)
        cl = self.closure(V)
        Z = [list(x) for x in cl] + [self.pad(r) for r in self.rel]
        keep = set(2 * u + c for u in U for c in (0, 1))
        alphas = sub_coord_space(Z, keep, 2 * self.n)
        newids = self._add_vertices(U)
        for a in alphas:
            self.rel.append(self._tau(a, U, newids, True))
        self.steps.append(('copy', list(U), V, newids))

    def attach_link(self, U, u, w, link):
        assert len(set(U)) == len(U) and all(0 <= x < self.n for x in U) and u in U and 0 <= w < self.n
        keep = set(2 * x + c for x in U for c in (0, 1))
        alphas = sub_coord_space([self.pad(r) for r in self.rel], keep, 2 * self.n)
        newids = self._add_vertices(U)
        for a in alphas:
            self.rel.append(self._tau(a, U, newids, False))
        up = newids[U.index(u)]
        if link == 'id':
            V = [('std', w, (1, 0)), ('std', w, (0, 1))]
            for c in (0, 1):
                r = [Fraction(0)] * (2 * self.n)
                r[2 * up + c] = Fraction(1)
                r[2 * w + c] = Fraction(-1)
                self.rel.append(r)
        else:
            a, b = link
            assert (a, b) in self.R
            V = [('std', w, (a, b))]
            r = [Fraction(0)] * (2 * self.n)
            r[2 * up], r[2 * up + 1] = Fraction(a), Fraction(b)
            r[2 * w] -= a
            r[2 * w + 1] -= b
            self.rel.append(r)
        self.steps.append(('link', list(U), V, newids))


def parse_ref(x):
    if x[0] == 'amb':
        return ('amb', int(x[1]))
    return ('std', int(x[0]), (int(x[1][0]), int(x[1][1])))


def verify_lemma(L, lookup=None, depth=0):
    """Check the copy-lemma proof of a linear entropy inequality; return (base letters, {frozenset: coef}).
    lookup(id, depth) returns a verified lemma for "apply" proof entries."""
    if depth > 100000:
        raise SystemExit("FAIL: lemma references too deep")
    base, letters = L['base'], L['vars']
    if len(set(letters)) != len(letters) or letters[:len(base)] != base or not base:
        raise SystemExit("FAIL: lemma variables malformed")
    have = list(base)
    steps = []
    for st in L['steps']:
        new, src, over = st['new'], st['src'], st['over']
        if len(new) != len(src) or not new or len(set(new)) != len(new) or len(set(over)) != len(over):
            raise SystemExit("FAIL: lemma copy step malformed")
        if any(x in have for x in new) or any(x not in have for x in over):
            raise SystemExit("FAIL: lemma copy step uses unknown or reused letters")
        if any(not g or any(x not in have for x in g) for g in src):
            raise SystemExit("FAIL: lemma copy source not existing")
        steps.append((new, src, over, list(have)))
        have += list(new)
    if have != list(letters):
        raise SystemExit("FAIL: lemma variable order must follow the copy steps")
    allv = frozenset(letters)
    tot = {}

    def add(S, c):
        S = frozenset(S)
        if S:
            tot[S] = tot.get(S, 0) + c
    for item in L['proof']:
        kind, m = item[0], Fraction(item[-1])
        if kind == 'mono':
            x = item[1]
            if m < 0 or x not in allv:
                raise SystemExit("FAIL: lemma mono entry")
            add(allv, m)
            add(allv - {x}, -m)
        elif kind == 'sub':
            x, y, K = item[1], item[2], item[3]
            if m < 0 or x == y or x not in allv or y not in allv or x in K or y in K or any(z not in allv for z in K):
                raise SystemExit("FAIL: lemma sub entry")
            K = set(K)
            add(K | {x}, m)
            add(K | {y}, m)
            add(K | {x, y}, -m)
            add(K, -m)
        elif kind == 'eqlaw':
            t, S = int(item[1]), item[2]
            new, src, over, old = steps[t]
            if len(set(S)) != len(S) or any(x not in new and x not in over for x in S) or not any(x in new for x in S):
                raise SystemExit("FAIL: lemma eqlaw entry")
            img = set(x for x in S if x in over)
            for x in S:
                if x in new:
                    img |= set(src[new.index(x)])
            add(S, m)
            add(img, -m)
        elif kind == 'ci':
            t = int(item[1])
            new, src, over, old = steps[t]
            add(set(new) | set(over), m)
            add(old, m)
            add(set(new) | set(old), -m)
            add(over, -m)
        elif kind == 'apply':
            # a verified lemma applied to joint variables: item = ['apply', id, [arg per base letter], mult]
            if m < 0 or lookup is None:
                raise SystemExit("FAIL: lemma apply entry")
            sub_base, sub_coef = lookup(str(item[1]), depth + 1)
            args = item[2]
            if len(args) != len(sub_base) or any(not a or any(x not in allv for x in a) for a in args):
                raise SystemExit("FAIL: lemma apply arguments")
            amap = dict(zip(sub_base, args))
            for S, cS in sub_coef.items():
                add(set(x for y in S for x in amap[y]), m * cS)
        else:
            raise SystemExit(f"FAIL: unknown lemma proof entry {kind}")
    coef = {}
    for k, v in L['coef'].items():
        S = frozenset(k)
        if not S or len(S) != len(k) or not S <= frozenset(base):
            raise SystemExit("FAIL: lemma coefficient on a non-base subset")
        coef[S] = coef.get(S, 0) + Fraction(v)
    keys = set(tot) | set(coef)
    if any(tot.get(S, 0) != coef.get(S, 0) for S in keys):
        raise SystemExit("FAIL: lemma proof does not sum to the stated inequality")
    return base, coef


def main(path):
    C = json.load(open(path))
    conf = Conf(C['slopes'])
    for st in C['steps']:
        if 'link' in st:
            U, u, w, lk = st['link']
            conf.attach_link(list(U), u, w, 'id' if lk == 'id' else tuple(lk))
        else:
            conf.attach(st['U'], [(v, tuple(s)) for v, s in st['V']])
    conf.extra = [list(f) for f in C.get('extra', [])]
    print(f"configuration: {conf.n} vertices, relation rank {len(conf.relrows())}, "
          f"{len(conf.extra)} extra forms")
    cache = {}

    def cl(gens):
        return conf.closure([parse_ref(g) if not isinstance(g, tuple) else g for g in gens], cache)

    parent = {}

    def find(a):
        parent.setdefault(a, a)
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a

    def union(a, b):
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[ra] = rb

    empty = frozenset()
    for e in C['eqlaw']:
        t = e['step']
        kind, U, V, newids = conf.steps[t]
        gens = [parse_ref(g) for g in e['gens']]
        img = []
        for g in gens:
            if g[0] != 'std':
                raise SystemExit("FAIL: eqlaw generator must be a standard form")
            if kind == 'copy' and g in V:
                img.append(g)
            elif g[1] in U:
                img.append(('std', newids[U.index(g[1])], g[2]))
            else:
                raise SystemExit(f"FAIL: eqlaw generator {g} not allowed for step {t}")
        union(cl(gens), cl(img))

    total = {}
    lemmas, active = {}, set()

    def lookup(lid, depth):
        """Verify lemma lid once (its proof may apply other lemmas of the certificate; cycles are rejected)."""
        if lid in lemmas:
            return lemmas[lid]
        if lid in active or lid not in C.get('lemmas', {}):
            raise SystemExit(f"FAIL: lemma {lid} missing or cyclic")
        active.add(lid)
        lemmas[lid] = verify_lemma(C['lemmas'][lid], lookup, depth)
        active.discard(lid)
        return lemmas[lid]

    def add(F, coef):
        if F == empty:
            return
        k = find(F)
        total[k] = total.get(k, 0) + coef

    for lid in C.get('lemmas', {}):      # verify every lemma (in listed order, so chains recurse shallowly)
        lookup(lid, 0)
    for r in C['rows']:
        m = Fraction(r['mult'])
        if r['type'] in ('sub', 'mono'):
            if m < 0:
                raise SystemExit("FAIL: negative multiplier on Shannon row")
            K = [parse_ref(g) for g in r['K']]
            i = parse_ref(r['i'])
            if r['type'] == 'sub':
                j = parse_ref(r['j'])
                add(cl(K + [i]), m)
                add(cl(K + [j]), m)
                add(cl(K + [i, j]), -m)
                add(cl(K), -m)
            else:
                add(cl(K + [i]), m)
                add(cl(K), -m)
        elif r['type'] == 'matus':
            if m < 0:
                raise SystemExit("FAIL: negative multiplier on matus row")
            sv = int(r['s'])
            if sv < 1:
                raise SystemExit("FAIL: matus row needs s >= 1")
            A_ = [parse_ref(g) for g in r['a']]; B_ = [parse_ref(g) for g in r['b']]
            C_ = [parse_ref(g) for g in r['c']]; D_ = [parse_ref(g) for g in r['d']]

            def Iq(x, y, z, coef):
                add(cl(x + z), coef)
                add(cl(y + z), coef)
                add(cl(x + y + z), -coef)
                add(cl(z), -coef)
            cc = Fraction(sv * (sv + 1), 2)
            Iq(B_, C_, A_, m)
            Iq(A_, B_, [], -sv * m)
            Iq(A_, B_, C_, sv * m)
            Iq(A_, B_, D_, sv * m)
            Iq(C_, D_, [], sv * m)
            Iq(A_, C_, B_, cc * m)
            Iq(A_, B_, C_, cc * m)
        elif r['type'] == 'lemma':
            if m < 0:
                raise SystemExit("FAIL: negative multiplier on lemma row")
            base, coef = lookup(str(r['lemma']), 0)
            if len(r['args']) != len(base):
                raise SystemExit("FAIL: lemma row needs one argument per base variable")
            args = {x: [parse_ref(g) for g in a] for x, a in zip(base, r['args'])}
            for S, cS in coef.items():
                add(cl([g for x in sorted(S) for g in args[x]]), m * cS)
        elif r['type'] == 'ci':
            t = r['step']
            kind, U, V, newids = conf.steps[t]
            old = list(range(newids[0]))
            oldg = [('std', v, s) for v in old for s in conf.SL]
            newg = [('std', v, s) for v in newids for s in conf.SL]
            add(cl(list(V) + newg), m)
            add(cl(oldg), m)
            add(cl(oldg + newg), -m)
            add(cl(list(V)), -m)
        else:
            raise SystemExit(f"FAIL: unknown row type {r['type']}")
    add(cl([('std', 0, (1, 0)), ('std', 0, (0, 1))]), Fraction(1))
    lam = {}
    for k, v in C['lambda'].items():
        a, b = (int(x) for x in k.split(','))
        lam[(a, b)] = Fraction(v)
        if lam[(a, b)] < 0:
            raise SystemExit("FAIL: negative lambda")
        if (a, b) not in conf.R:
            raise SystemExit("FAIL: lambda on a slope outside R")
    target = {}
    for s, v in lam.items():
        F = find(cl([('std', 0, s)]))
        target[F] = target.get(F, 0) + v
    keys = set(total) | set(target)
    bad = [k for k in keys if total.get(k, 0) != target.get(k, 0)]
    if bad:
        print(f"FAIL: identity does not hold on {len(bad)} classes")
        for k in bad[:5]:
            print("   ", total.get(k, 0), target.get(k, 0))
        sys.exit(1)
    Ctot = sum(lam.values())
    print("PASS: H(X,Y) <= " + " + ".join(f"{v}*H({s[0]}X+{s[1]}Y)" for s, v in sorted(lam.items())))
    print(f"constant C = {Ctot} = {float(Ctot):.12f}")
    return Ctot


if __name__ == '__main__':
    main(sys.argv[1])
