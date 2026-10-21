"""Matus/ZY cutting planes on an extended LP, saving cut definitions, then exact certificate.
python ns_cert.py NAME SCHEME FORMS MAXRANK ROUNDS [SVALS e.g. 1,2]"""
import sys, time, json
import numpy as np
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from eng import Lattice
from fastlp import build_lp, solve_lp
from kt import kt116, kt74
from nonshannon import join_table, matus_terms, most_violated
from sepnb import most_violated_nb
from cert_fast import certify_fast
name, scheme, formsf, maxrank, rounds = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]), int(sys.argv[5])
svals = tuple(int(x) for x in sys.argv[6].split(',')) if len(sys.argv) > 6 and not sys.argv[6].startswith('smax') else (1, 2)
REFINE = len(sys.argv) > 7 and sys.argv[7] == 'refine'
SMAX = int(sys.argv[6][4:]) if len(sys.argv) > 6 and sys.argv[6].startswith('smax') else 0
if SMAX:
    svals = ()
if scheme in ('kt116', 'kt74'):
    cfg = kt116() if scheme == 'kt116' else kt74()
else:
    from peval import build as pbuild, RS as PRS
    _J = json.load(open(scheme))
    cfg = pbuild(PRS[_J['R']], _J['steps'])
    scheme = 'kt116' if _J['R'] == 3 else 'kt74'
thr = 11 / 6 if scheme == 'kt116' else 7 / 4
forms = json.load(open(formsf)) if formsf != 'none' else []
lat = Lattice(cfg, verbose=False, extra_amb=forms)
t0 = time.time()
J = join_table(lat)
cand = [f for f in range(1, lat.nflats) if lat.rank[f] <= maxrank]
print(f'{name}: flats {lat.nflats} candidates {len(cand)}', flush=True)
defs, extra, seen = [], [], set()
import os
if os.environ.get('INIT_CUTS'):
    for dd in json.load(open(os.environ['INIT_CUTS']))['defs']:
        kind, s_, a_, b_, c_, d_ = dd
        dct = matus_terms(J, a_, b_, c_, d_, s_)
        key = tuple(sorted(dct.items()))
        if dct and key not in seen:
            seen.add(key); extra.append(dct); defs.append(('matus', s_, a_, b_, c_, d_))
    print(f' loaded {len(defs)} initial cuts', flush=True)
for it in range(rounds):
    L = build_lp(cfg, lat, extra_rows=[(d, 0.0, np.inf) for d in extra])
    S = solve_lp(L, opts={'solver': 'ipm', 'run_crossover': 'on'})
    colof = L['colof']; xv = S['col_value']
    h = np.where(colof >= 0, xv[np.maximum(colof, 0)], 0.0)
    if SMAX:
        from sepnb import most_violated_alls
        viol = most_violated_alls(h, J, cand, smax=SMAX, top=400, threads=12)
    else:
        viol = most_violated_nb(h, J, cand, svals=svals, top=400, threads=12)
    if REFINE and viol:
        from sepnb import refine
        viol = sorted(set(viol) | set(refine(h, J, viol[:200], list(range(1, lat.nflats)))))[:500]
    print(f' round {it}: LP {S["value"]:.9f} cuts {len(extra)} violated {len(viol)}  {time.time()-t0:.0f}s', flush=True)
    json.dump(dict(defs=defs, value=S['value']), open(f'runs/{name}_cuts.json', 'w'))
    if not viol:
        break
    for (v, s, a, b, c, d) in viol:
        dct = matus_terms(J, a, b, c, d, s)
        key = tuple(sorted(dct.items()))
        if key not in seen and dct:
            seen.add(key); extra.append(dct); defs.append(('matus', s, a, b, c, d))
# final exact certificate (only if below the classical bound)
L = build_lp(cfg, lat, extra_rows=[(d, 0.0, np.inf) for d in extra])
if S['value'] > thr - 1e-7:
    print(' no improvement over the classical bound; no certificate', flush=True)
    sys.exit(0)
S = solve_lp(L, opts={'solver': 'ipm', 'run_crossover': 'on'})
print(f' final LP (crossover) {S["value"]!r} {S["status"]}', flush=True)
tot, Jc = certify_fast(cfg, lat, L, S, f'certs/{name}.json', extra_defs=defs)
print(' certified', tot, float(tot), flush=True)
