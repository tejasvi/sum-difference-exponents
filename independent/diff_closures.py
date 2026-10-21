#!/usr/bin/env python3
"""Differential test: compare check630.py's relation space and closures with indep_check.py's, row by row."""
import importlib.util, json, os, sys
from fractions import Fraction
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import indep_check
spec = importlib.util.spec_from_file_location('c630', os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'checker', 'check630.py'))
c630 = importlib.util.module_from_spec(spec); spec.loader.exec_module(c630)
C = json.load(open(sys.argv[1]))
conf = c630.Conf(C['slopes'])
for st in C['steps']:
    conf.attach(st['U'], [(v, tuple(s)) for v, s in st['V']])
conf.extra = [list(f) for f in C.get('extra', [])]
P = indep_check.build(C)
n = P.n
# relation spaces: check630 rel (ambient vectors) vs kernel of my parametrization
M = [[P.vx[v][j] if c == 0 else P.vy[v][j] for v in range(n) for c in (0, 1)] for j in range(P.k)]
myker = indep_check.nullspace_rows(indep_check.rref_basis(M, 2 * n), 2 * n)
theirs = indep_check.rref_basis([[Fraction(a) for a in r] for r in conf.rel], 2 * n)
mine = indep_check.rref_basis(myker, 2 * n)
print('relation spaces equal:', theirs == mine, 'rank', len(theirs), len(mine))
# closures: for every generator set appearing in the rows, compare span dimension and ground membership
def refs_of(r):
    out = []
    K = r.get('K', [])
    if r['type'] == 'sub':
        out = [K + [r['i']], K + [r['j']], K + [r['i'], r['j']], K]
    elif r['type'] == 'mono':
        out = [K + [r['i']], K]
    elif r['type'] == 'matus':
        a, b, c, d = r['a'], r['b'], r['c'], r['d']
        for x, y, z in ((a, b, c), (a, c, b), (b, c, a), (a, b, d), (c, d, []), (a, b, [])):
            out += [x + z, y + z, x + y + z, z]
        out = [g for g in out if g]
    return out
ground = conf.ground()
nmis = 0; ntest = 0
for r in C['rows']:
    for gens in refs_of(r):
        g630 = [c630.parse_ref(g) for g in gens]
        cl630 = conf.closure(g630)
        vecs = [indep_check.ref_vec(P, g, C['extra']) for g in gens]
        W = P.closure(vecs)
        # map each ground element to my param vector; membership in W vs membership in cl630
        R = conf.relrows()
        for gr in ground:
            nfv = conf.nf(conf.vec(gr), R)
            in630 = nfv is not None and nfv in cl630
            if gr[0] == 'amb':
                pv = P.amb(conf.extra[gr[1]])
            else:
                pv = P.form(gr[1], gr[2])
            inmine = indep_check.in_span(W, pv, P.k)
            if nfv is None:
                inmine = True; in630 = True
            ntest += 1
            if in630 != inmine:
                nmis += 1
print(f'closure membership comparisons: {ntest}, mismatches: {nmis}')
