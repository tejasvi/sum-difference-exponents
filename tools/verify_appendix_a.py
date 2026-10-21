#!/usr/bin/env python3
"""Check the identity (A.1) of Appendix A directly from the printed tables.

Usage: python3 tools/verify_appendix_a.py checker/check630.py tools/appendix_a_rows.tex tools/appendix_a_identifications.tex

The configuration is the one of Section 3.2 (three copy steps, rebuilt by check630's Conf class); the
cross forms, the 72 rows I(A;B|C) with weights w_k and the 16 identifications are parsed from the LaTeX
tables of the paper.  The script verifies, in exact arithmetic,

    459 H(X,Y) + sum_k w_k I_k - 220 CI_1 - 79 CI_2 - 69 CI_3 = 314 H(X) + 302 H(Y) + 225 H(X+Y)

after every joint entropy is replaced by the entropy of the closure of its forms and the identifications
are applied.
"""
import importlib.util, re, sys
from fractions import Fraction

spec = importlib.util.spec_from_file_location('c630', sys.argv[1])
c630 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(c630)
ROWS, IDENT = sys.argv[2], sys.argv[3]

conf = c630.Conf([(1, 0), (0, 1), (1, 1)])
conf.attach([0], [(0, (1, 0))])                      # (S1) copy of g0 over x0
conf.attach([0, 1], [(0, (0, 1)), (1, (0, 1))])      # (S2) copy of (g0, g1) over (y0, y1)
conf.attach([0, 1], [(0, (1, 1)), (1, (0, 1))])      # (S3) copy of (g0, g1) over (x0 + y0, y1)
assert conf.n == 6 and len(conf.relrows()) == 7
# free coordinate -> ambient index (x0, y0, x1, y1, x2, y2, x3, y3, x4, y4, x5, y5)
AMB = {'x_0': 0, 'y_0': 1, 'y_1': 3, 'x_2': 4, 'x_4': 8}


def parse_form(t):
    t = t.replace(' ', '').replace('{', '').replace('}', '')
    v = [0] * 12
    for sign, coef, var in re.findall(r'([+-]?)(\d*)([xy]_\d)', t):
        c = int(coef) if coef else 1
        v[AMB[var]] += -c if sign == '-' else c
    assert any(v), t
    return v


def parse_tuple(t):
    t = t.strip()
    if t.startswith('(') and t.endswith(')'):
        t = t[1:-1]
    return [parse_form(x) for x in t.split(',') if x.strip()]


forms = []


def ref(v):
    """Ground element for an ambient vector: register it as an extra form."""
    if v not in forms:
        forms.append(v)
    return ('amb', forms.index(v))


rows = []
for line in open(ROWS):
    cells = [c.strip() for c in line.strip().rstrip('\\').split('&')]
    for w, expr in ((cells[0], cells[1]), (cells[2], cells[3])):
        if not w:
            continue
        m = re.fullmatch(r'\$I\((.*)\)\$', expr)
        body = m.group(1)
        if '\\,|\\,' in body:
            ab, c = body.split('\\,|\\,')
        else:
            ab, c = body, ''
        depth, cut = 0, None
        for i, ch in enumerate(ab):
            depth += ch == '('
            depth -= ch == ')'
            if ch == ';' and depth == 0:
                cut = i
        a, b = ab[:cut], ab[cut + 1:]
        rows.append((int(w), parse_tuple(a), parse_tuple(b), parse_tuple(c) if c else []))
assert len(rows) == 72, len(rows)
idents = []
for line in open(IDENT):
    step, eq = [c.strip() for c in line.strip().rstrip('\\').split('&')]
    m = re.fullmatch(r'\$H\[(.*)\]=H\[(.*)\]\$', eq)
    idents.append((int(step), parse_tuple(m.group(1)), parse_tuple(m.group(2))))
assert len(idents) == 16, len(idents)

# register all forms, then fix the ground set
for w, a, b, c in rows:
    for v in a + b + c:
        ref(v)
for t, s1, s2 in idents:
    for v in s1 + s2:
        ref(v)
conf.extra = forms
cache = {}


def cl(vs):
    return conf.closure([ref(v) for v in vs], cache)


parent = {}


def find(x):
    parent.setdefault(x, x)
    while parent[x] != x:
        parent[x] = parent[parent[x]]
        x = parent[x]
    return x


for t, s1, s2 in idents:
    a, b = find(cl(s1)), find(cl(s2))
    parent[a] = b

tot = {}


def add(F, c):
    if not F:
        return
    k = find(F)
    tot[k] = tot.get(k, 0) + c


def H(vs, c):
    add(cl(vs), Fraction(c))


std = lambda v, s: [conf.vec(('std', v, s))]
X0, Y0, S0 = std(0, (1, 0))[0], std(0, (0, 1))[0], std(0, (1, 1))[0]
H([X0, Y0], 459)
for w, a, b, c in rows:
    H(a + c, w); H(b + c, w); H(a + b + c, -w); H(c, -w)
# CI_t = H(V, U') + H(O) - H(O, U') - H(V)
allstd = lambda vs: [conf.vec(('std', v, s)) for v in vs for s in conf.SL]
for (t, O, Up, V), wt in zip([(1, [0], [1], [X0]), (2, [0, 1], [2, 3], [Y0, std(1, (0, 1))[0]]),
                              (3, [0, 1, 2, 3], [4, 5], [S0, std(1, (0, 1))[0]])], (-220, -79, -69)):
    H(V + allstd(Up), wt); H(allstd(O), wt); H(allstd(O) + allstd(Up), -wt); H(V, -wt)
target = {}
for v, c in ((X0, 314), (Y0, 302), (S0, 225)):
    k = find(cl([v]))
    target[k] = target.get(k, 0) + c
bad = [k for k in set(tot) | set(target) if tot.get(k, 0) != target.get(k, 0)]
print('rows', len(rows), 'identifications', len(idents), 'closed sets', len(set(cache.values())))
if bad:
    print('FAIL: identity (A.1) does not hold on', len(bad), 'classes')
    sys.exit(1)
print('PASS: identity (A.1) holds exactly')
