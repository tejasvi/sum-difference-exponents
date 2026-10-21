"""Certify from (forms, cuts) for the KT 11/6 configuration: python certify_fc.py NAME FORMS CUTS"""
import sys, json
import numpy as np
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from eng import Lattice
from fastlp import build_lp, solve_lp
from kt import kt116
from nonshannon import matus_terms
from sepnb import join_partial, PJ
from cert_fast import certify_fast
name, formsf, cutsf = sys.argv[1:4]
cfg = kt116(); forms = json.load(open(formsf))
lat = Lattice(cfg, verbose=False, extra_amb=forms)
defs = [tuple(d) for d in json.load(open(cutsf))['defs']]
flats = sorted(set(x for d in defs for x in d[2:]))
Jp, col = join_partial(lat, flats); J = PJ(Jp, col)
extra, D, seen = [], [], set()
for d in defs:
    dct = matus_terms(J, d[2], d[3], d[4], d[5], d[1])
    key = tuple(sorted(dct.items()))
    if dct and key not in seen:
        seen.add(key); extra.append(dct); D.append(('matus', d[1], d[2], d[3], d[4], d[5]))
L = build_lp(cfg, lat, extra_rows=[(dd, 0.0, np.inf) for dd in extra])
import os
OPTS = json.loads(os.environ.get('LPOPTS', '{"solver": "ipm", "run_crossover": "on", "ipm_optimality_tolerance": 1e-10, "primal_feasibility_tolerance": 1e-10, "dual_feasibility_tolerance": 1e-10}'))
S = solve_lp(L, opts=OPTS)
print(name, 'flats', lat.nflats, 'cuts', len(D), 'LP', repr(S['value']), S['status'], flush=True)
tot, Jc = certify_fast(cfg, lat, L, S, f'certs/{name}.json', extra_defs=D)
print('certified', tot, float(tot), flush=True)
