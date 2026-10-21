#!/usr/bin/env python3
"""Verifier for 'lemma' entries of the certificates read by checker/check630.py. It re-implements the lemma
check of check630.py, following the same steps.  A lemma states  sum_S coef_S H(S) >= 0  over nonempty subsets S of its base letters, for ALL discrete
random variables.  Its proof works over the lemma's variables (base letters followed by letters introduced by copy steps):
  copy step t: new letters n_1..n_k, src groups g_1..g_k (each a nonempty set of existing letters, taken jointly), over
    (a set of existing letters).  Copy lemma: such new variables exist with (n, over) equal in law to (g, over) and n
    conditionally independent of all existing variables given over.  Hence
      eqlaw(t, S):  H(S) - H(phi S) = 0   for S within n u over meeting n, phi(n_i) = g_i (union);
      ci(t):        H(n u over) + H(old) - H(n u old) - H(over) = 0, old = all letters existing before step t.
  proof items: ['mono', x, m] (m >= 0): H(all) - H(all - x);  ['sub', x, y, K, m] (m >= 0): I(x;y|K);
    ['eqlaw', t, S, m], ['ci', t, m] (any sign);  ['apply', id, args, m] (m >= 0): another lemma of the same certificate,
    verified first (dependency graph must be acyclic), with its base letters replaced by the letter sets args.
  The proof is accepted iff the multiplier-weighted sum equals coef on base subsets and 0 on every other subset."""
from fractions import Fraction


class LemmaError(Exception):
    pass


def _fs(x):
    return frozenset(x)


def verify_one(L, sub_verified):
    base, letters = list(L['base']), list(L['vars'])
    if not base or letters[:len(base)] != base or len(set(letters)) != len(letters):
        raise LemmaError('variables malformed')
    existing = list(base)
    steps = []
    for st in L['steps']:
        new, src, over = list(st['new']), [list(g) for g in st['src']], list(st['over'])
        if not new or len(new) != len(src) or len(set(new)) != len(new) or len(set(over)) != len(over):
            raise LemmaError('copy step malformed')
        if any(x in existing for x in new) or any(x not in existing for x in over):
            raise LemmaError('copy step uses unknown or reused letters')
        if any(not g or any(x not in existing for x in g) for g in src):
            raise LemmaError('copy source not existing')
        steps.append((new, src, over, list(existing)))
        existing += new
    if existing != letters:
        raise LemmaError('letters must follow the copy steps in order')
    ALL = _fs(letters)
    tot = {}

    def add(S, c):
        S = _fs(S)
        if S:
            tot[S] = tot.get(S, Fraction(0)) + c
    for item in L['proof']:
        kind = item[0]
        m = Fraction(item[-1])
        if kind == 'mono':
            x = item[1]
            if m < 0 or x not in ALL:
                raise LemmaError('mono entry')
            add(ALL, m); add(ALL - {x}, -m)
        elif kind == 'sub':
            x, y, K = item[1], item[2], set(item[3])
            if m < 0 or x == y or x not in ALL or y not in ALL or x in K or y in K or not K <= ALL:
                raise LemmaError('sub entry')
            add(K | {x}, m); add(K | {y}, m); add(K | {x, y}, -m); add(K, -m)
        elif kind == 'eqlaw':
            t, S = item[1], list(item[2])
            if not (isinstance(t, int) and not isinstance(t, bool)) or not 0 <= t < len(steps):
                raise LemmaError('eqlaw step index')
            new, src, over, old = steps[t]
            if len(set(S)) != len(S) or any(x not in new and x not in over for x in S) or not any(x in new for x in S):
                raise LemmaError('eqlaw set')
            img = set(x for x in S if x in over)
            for x in S:
                if x in new:
                    img |= set(src[new.index(x)])
            add(S, m); add(img, -m)
        elif kind == 'ci':
            t = item[1]
            if not (isinstance(t, int) and not isinstance(t, bool)) or not 0 <= t < len(steps):
                raise LemmaError('ci step index')
            new, src, over, old = steps[t]
            add(set(new) | set(over), m); add(old, m); add(set(new) | set(old), -m); add(over, -m)
        elif kind == 'apply':
            lid, args = str(item[1]), [list(a) for a in item[2]]
            if m < 0:
                raise LemmaError('apply multiplier negative')
            sbase, scoef = sub_verified(lid)
            if len(args) != len(sbase) or any(not a or any(x not in ALL for x in a) for a in args):
                raise LemmaError('apply arguments')
            amap = dict(zip(sbase, args))
            for S, c in scoef.items():
                add(set(x for y in S for x in amap[y]), m * c)
        else:
            raise LemmaError(f'unknown proof entry {kind}')
    coef = {}
    for k, v in L['coef'].items():
        S = _fs(k)
        if not S or len(S) != len(k) or not S <= _fs(base):
            raise LemmaError('coefficient on a non-base subset')
        coef[S] = coef.get(S, Fraction(0)) + Fraction(v)
    for S in set(tot) | set(coef):
        if tot.get(S, Fraction(0)) != coef.get(S, Fraction(0)):
            raise LemmaError('proof does not sum to the stated inequality')
    return base, coef


def verify_all(lemmas):
    """Verify every lemma, resolving 'apply' dependencies by DFS with cycle detection (white/grey/black)."""
    state, done = {}, {}

    def visit(lid):
        if lid not in lemmas:
            raise LemmaError(f'lemma {lid} missing')
        if state.get(lid) == 'grey':
            raise LemmaError(f'cycle through lemma {lid}')
        if state.get(lid) == 'black':
            return done[lid]
        state[lid] = 'grey'
        res = verify_one(lemmas[lid], visit)
        state[lid] = 'black'
        done[lid] = res
        return res
    # iterative-deepening friendly order: verify in sorted dependency-free order by trying each
    import sys
    sys.setrecursionlimit(100000)
    for lid in lemmas:
        visit(lid)
    return done
