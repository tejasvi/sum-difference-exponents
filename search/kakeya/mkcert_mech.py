import sys, json
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from eng import Lattice
from fastlp import build_lp, solve_lp
from kt import kt116
from cert_fast import certify_fast
forms = json.load(open(sys.argv[1])); out = sys.argv[2]
cfg = kt116(); lat = Lattice(cfg, verbose=False, extra_amb=forms)
L = build_lp(cfg, lat, verbose=True)
S = solve_lp(L)   # simplex for a vertex solution
print('LP', repr(S['value']), lat.nflats)
tot, J = certify_fast(cfg, lat, L, S, out)
print(tot, float(tot))
