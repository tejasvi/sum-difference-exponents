#!/usr/bin/env python3
"""Split the certificate of Theorem 1.3 into its configuration part and its grid part.

Usage: python3 tools/split_pair.py checker/check3.py certs/pair_exponent.json

The script reads the checker, adds in memory two accumulators to it (one for the grid rows, whose types start with
g_, and one for all other rows), runs it on the certificate, and prints
  - the weighted sum of the configuration rows, an inequality between L, S and finitely many h(i, j)
    (Proposition 4.1 of the paper);
  - the weighted sum of the grid rows (Lemma 4.2);
  - their sum, which is den * (lambda * S - L) >= 0;
  - the number of distinct closed sets H(cl G) that the checker uses, in total and for each copy.
All joint entropies cancel inside each part, and the h(i, j) cancel between the parts; the script asserts both.
The checker file itself is not modified.
"""
import contextlib, io, math, re, sys, types
from fractions import Fraction

if not __debug__:
    raise SystemExit("this script relies on assert statements; run it without -O")

src = open(sys.argv[1]).read()
reps = [
    ("""    acc = Acc()
    counts = {}""",
     """    acc = Acc()
    accc = Acc()
    accg = Acc()
    counts = {}"""),
    ("""        for term, cf in R.t.items():
            acc.add(term, m * cf)""",
     """        for term, cf in R.t.items():
            acc.add(term, m * cf)
            (accg if t.startswith('g_') else accc).add(term, m * cf)"""),
    ("""    print(f"PASS: L <= lambda * S with lambda = {lam} = {float(lam):.12f}")""",
     """    print(f"PASS: L <= lambda * S with lambda = {lam} = {float(lam):.12f}")
    SPLIT['config'] = {k: v for k, v in accc.t.items() if v != 0}
    SPLIT['grid'] = {k: v for k, v in accg.t.items() if v != 0}
    SPLIT['lambda'] = lam"""),
]
for a, b in reps:
    assert src.count(a) == 1, ('the checker does not have the expected form', a[:40])
    src = src.replace(a, b)
mod = types.ModuleType('check3_split')
mod.__dict__['SPLIT'] = {}
mod.__dict__['__name__'] = 'check3_split'
exec(compile(src, 'check3_split', 'exec'), mod.__dict__)
seen = set()
orig = mod.Hterm


def counting_hterm(cp, gens):
    t = orig(cp, gens)
    if t is not None:
        seen.add(t)
    return t


mod.Hterm = counting_hterm
buf = io.StringIO()
with contextlib.redirect_stdout(buf):
    ok = mod.check(sys.argv[2])
assert ok, buf.getvalue()
print(buf.getvalue().strip())
S = mod.SPLIT
lam = S['lambda']
for part in ('config', 'grid'):
    assert all(k[0] in ('L', 'S', 'h') for k in S[part]), ('a joint entropy does not cancel in the', part, 'part')
den = 1
for part in ('config', 'grid'):
    for v in S[part].values():
        den = den * v.denominator // math.gcd(den, v.denominator)
A = {k: int(v * den) for k, v in S['config'].items()}
B = {k: int(v * den) for k, v in S['grid'].items()}
L, Sv = ('L',), ('S',)
hk = sorted({k for k in list(A) + list(B) if k[0] == 'h'}, key=lambda k: (k[1], k[2]))
assert all(A.get(k, 0) + B.get(k, 0) == 0 for k in hk), 'the h(i, j) do not cancel between the parts'
assert A.get(L, 0) + B.get(L, 0) == -den and A.get(Sv, 0) + B.get(Sv, 0) == lam * den, 'the parts do not sum to lambda*S - L'


def show(P):
    """The inequality 0 <= sum P[k] k, written with positive coefficients on both sides."""
    keys = [L, Sv] + hk
    name = lambda k: {'L': 'L', 'S': 'S'}.get(k[0]) or 'h(%d,%d)' % (k[1], k[2])
    lhs = ['%d %s' % (-P[k], name(k)) for k in keys if P.get(k, 0) < 0]
    rhs = ['%d %s' % (P[k], name(k)) for k in keys if P.get(k, 0) > 0]
    return '  ' + ' + '.join(lhs) + '\n  <= ' + ' + '.join(rhs)


print('configuration rows (Proposition 4.1):')
print(show(A))
print('grid rows (Lemma 4.2):')
print(show(B))
print('sum: %d L <= %d S, i.e. L <= %s S' % (den, int(lam * den), lam))
by_copy = {c: sum(1 for t in seen if t[1] == c) for c in sorted({t[1] for t in seen})}
print('closed sets used: %d (%s)' % (len(seen), ', '.join('copy %s: %d' % kv for kv in by_copy.items())))
