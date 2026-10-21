"""Certify from (forms, cuts) where cuts may be Matus ('matus', s, a, b, c, d), DFZ ('dfz', k, a, b, c, d) or
copy-lemma ('lem', id, a, b, c, d; lemma records in CUTS with _cuts.json -> _lemmas.json) rows
(DFZ entries without an exact copy-lemma proof in dfz/lemmas.json are dropped).  KT 11/6 configuration
(SCHEME=kt74 for 3c).  Optional SMAX drops Matus rows with s > SMAX.  python certify_fcd.py NAME FORMS CUTS"""
import sys, json, os
import numpy as np
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from eng import Lattice
from fastlp import build_lp, solve_lp
from kt import kt116, kt74
from nonshannon import matus_terms
from sepnb import join_partial, PJ
from dfzsep import dfz_terms
from cert_fast import certify_fast
import clsep
name, formsf, cutsf = sys.argv[1:4]
REG = json.load(open(cutsf.replace('_cuts.json', '_lemmas.json'))) if os.path.exists(cutsf.replace('_cuts.json', '_lemmas.json')) else {}
smax = int(os.environ.get('SMAX', '1000000'))
cfg = kt74() if os.environ.get('SCHEME') == 'kt74' else kt116()
forms = json.load(open(formsf))
lat = Lattice(cfg, verbose=False, extra_amb=forms)
defs = [tuple(d) for d in json.load(open(cutsf))['defs']]
W = {int(k): v for k, v in json.load(open('dfz/dfz214_raw.json')).items()}
proven = set(int(k) for k in json.load(open('dfz/lemmas.json')))
flats = sorted(set(x for d in defs for x in d[2:]))
Jp, col = join_partial(lat, flats); J = PJ(Jp, col)
extra, D, seen, dropped = [], [], set(), 0
for d in defs:
    if d[0] == 'matus':
        if d[1] > smax:
            dropped += 1; continue
        dct = matus_terms(J, d[2], d[3], d[4], d[5], d[1])
    elif d[0] == 'dfz':
        if d[1] not in proven:
            dropped += 1; continue
        dct = dfz_terms(J, d[2], d[3], d[4], d[5], W[d[1]])
    elif d[0] == 'lem':
        dct = clsep.lemma_terms(clsep.quad_flats(J, d[2], d[3], d[4], d[5]), REG[d[1]]['coef'])
    else:
        raise SystemExit(f'unsupported cut kind {d[0]}')
    key = tuple(sorted(dct.items()))
    if dct and key not in seen:
        seen.add(key); extra.append(dct); D.append(tuple(d))
L = build_lp(cfg, lat, extra_rows=[(dd, 0.0, np.inf) for dd in extra])
OPTS = json.loads(os.environ.get('LPOPTS', '{"solver": "ipm", "run_crossover": "on", "ipm_optimality_tolerance": 1e-10, "primal_feasibility_tolerance": 1e-10, "dual_feasibility_tolerance": 1e-10}'))
S = solve_lp(L, opts=OPTS)
nd = sum(1 for d in D if d[0] == 'dfz')
print(name, 'flats', lat.nflats, 'cuts', len(D), f'(dfz {nd}, dropped {dropped})', 'LP', repr(S['value']), S['status'],
      flush=True)
tot, Jc = certify_fast(cfg, lat, L, S, f'certs/{name}.json', extra_defs=D, lemma_registry=REG)
print('certified', tot, float(tot), flush=True)
