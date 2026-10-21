#!/usr/bin/env python3
"""Negative tests (generic; usage: neg_tests2.py CERT.json): every perturbation must be rejected by BOTH checkers
(check630.py, run as a subprocess on a temp copy, and indep_check.py, called in-process)."""
import copy
import json
import os
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import indep_check  # noqa: E402

CERT = os.path.expanduser(sys.argv[1])
CHECK630 = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'checker', 'check630.py')
TMP = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'negtmp5')
os.makedirs(TMP, exist_ok=True)

base = json.load(open(CERT))
tests = []


def T(name, fn, inj=True):
    C = copy.deepcopy(base)
    fn(C)
    tests.append((name, C, inj))


def scale_mult(i, f):
    def g(C):
        C['rows'][i]['mult'] = str(Fraction(C['rows'][i]['mult']) * f)
    return g


def add_mult(i, d):
    def g(C):
        C['rows'][i]['mult'] = str(Fraction(C['rows'][i]['mult']) + d)
    return g


def drop_row(i):
    def g(C):
        del C['rows'][i]
    return g


def drop_eq(i):
    def g(C):
        del C['eqlaw'][i]
    return g


def set_lam(key, d):
    def g(C):
        C['lambda'][key] = str(Fraction(C['lambda'][key]) + d)
        C['claimed_C'] = str(sum(Fraction(v) for v in C['lambda'].values()))
    return g


NR = len(base['rows'])
eps = Fraction(1, Fraction(base['claimed_C']).denominator)
T('identity (unperturbed, must PASS)', lambda C: None)
T('row0 mult * 1001/1000', scale_mult(0, Fraction(1001, 1000)))
T('row2 mult + eps', add_mult(2, eps))
T(f'row{NR // 2} mult - eps/2', add_mult(NR // 2, -eps / 2))
T('ci row mult + eps', add_mult([i for i, r in enumerate(base['rows']) if r['type'] == 'ci'][0], eps))
NR = len(base['rows'])
for i in sorted(set([0, 1, 5, NR // 3, (2 * NR) // 3, NR - 1])):
    T(f'drop row {i} ({base["rows"][i]["type"]})', drop_row(i))
T('lambda X - eps', set_lam('1,0', -eps))
T('lambda Y - eps', set_lam('0,1', -eps))
T('lambda S - eps', set_lam('1,1', -eps))
T('lambda S + eps (weaker target, still not an identity)', set_lam('1,1', eps))
for i in range(len(base['eqlaw'])):
    T(f'drop eqlaw {i} (step {base["eqlaw"][i]["step"]}, gens {base["eqlaw"][i]["gens"]})', drop_eq(i))


def ch_step2(C):
    C['steps'][2]['V'] = [[0, [1, 0]], [1, [0, 1]]]
T('step 2 glued on (x0, y1) instead of (s0, y1)', ch_step2)


def ch_step1(C):
    C['steps'][1]['V'] = [[0, [0, 1]]]
T('step 1 glued on y0 only', ch_step1)


USED = sorted({int(x[1]) for r in base['rows'] for x in r.get('K', []) + [r.get('i')] + ([r['j']] if 'j' in r else [])
               if x and x[0] == 'amb'})
E1, E2 = USED[0], USED[len(USED) // 2]


def ch_extra(C):
    C['extra'][E1] = [-a for a in C['extra'][E1]][:]
    f = C['extra'][E1]
    nz = [i for i, a in enumerate(f) if a != 0]
    f[nz[-1]] = -f[nz[-1]]
T(f'extra form {E1}: flip sign of last nonzero coordinate', ch_extra)


def ch_extra2(C):
    C['extra'][E2] = [0] * len(C['extra'][E2])
    C['extra'][E2][0] = 1
T(f'extra form {E2} replaced by x0', ch_extra2)


def neg_shannon(C):
    i = [i for i, r in enumerate(C['rows']) if r['type'] == 'sub'][0]
    C['rows'][i]['mult'] = str(-Fraction(C['rows'][i]['mult']))
T('negate a Shannon multiplier', neg_shannon)


def swap_ij(C):
    r = [r for r in C['rows'] if r['type'] == 'sub' and r['K']][3]
    r['j'] = [0, [1, 1]] if r['j'] != [0, [1, 1]] else [0, [0, 1]]
T('change j of a conditional sub row', swap_ij)
T('no injectivity rule (indep checker only; check630 runs unperturbed)', lambda C: None, inj=False)

if len(base['extra']) > 39 and base['extra'][39] == [1, 1, 0, 1, 1, 0, 0, 0, -1, 0, 0, 0]:
    def f39_set(newf):
        def g(C):
            C['extra'][39] = list(newf)
        return g
    T('extra form 39 (y4+s3): x4 coefficient flipped -> x0+y0+y1+x2+x4', f39_set([1, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0]))
    T('extra form 39 replaced by y4 - s3 = x0+y0-y1-x2-x4', f39_set([1, 1, 0, -1, -1, 0, 0, 0, -1, 0, 0, 0]))
    T('extra form 39 replaced by s3 alone (x2+y1)', f39_set([0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]))
    T('INFO extra form 39 scaled by 2 (same flat over Z; expected PASS)', f39_set([2, 2, 0, 2, 2, 0, 0, 0, -2, 0, 0, 0]))
    T('INFO extra form 39 negated (same flat; expected PASS)', f39_set([-1, -1, 0, -1, -1, 0, 0, 0, 1, 0, 0, 0]))

if len(base['extra']) > 41:
    def ex_set(j, newf):
        def g(C):
            C['extra'][j] = list(newf)
        return g
    if base['extra'][40] == [1, 1, 0, -1, -1, 0, 0, 0, -1, 0, 0, 0]:
        T('extra form 40 (y4-s3): x4 coefficient flipped -> x0+y0-y1-x2+x4', ex_set(40, [1, 1, 0, -1, -1, 0, 0, 0, 1, 0, 0, 0]))
        T('extra form 40 replaced by y4 alone (x0+y0-x4)', ex_set(40, [1, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0]))
        T('INFO extra form 40 negated (same flat; expected PASS)', ex_set(40, [-1, -1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0]))
    if base['extra'][41] == [1, 0, 0, -1, -1, 0, 0, 0, 0, 0, 0, 0]:
        T('extra form 41 (x0-s3): y1 coefficient flipped -> x0+y1-x2', ex_set(41, [1, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0]))
        T('extra form 41 replaced by x0+s3', ex_set(41, [1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]))

    if len(base['extra']) > 42 and base['extra'][42] == [0, 1, 0, 1, 1, 0, 0, 0, -1, 0, 0, 0]:
        T('extra form 42 (y4+s3-x0): x4 coefficient flipped -> y0+y1+x2+x4', ex_set(42, [0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0]))
        T('extra form 42 replaced by y4+s3 (form 39)', ex_set(42, [1, 1, 0, 1, 1, 0, 0, 0, -1, 0, 0, 0]))
        T('INFO extra form 42 negated (same flat; expected PASS)', ex_set(42, [0, -1, 0, -1, -1, 0, 0, 0, 1, 0, 0, 0]))




MI = [i for i, r in enumerate(base['rows']) if r['type'] == 'matus']


def mat_set(i, key, val):
    def g(C):
        C['rows'][i][key] = val
    return g


def mat_swap(i, k1, k2):
    def g(C):
        C['rows'][i][k1], C['rows'][i][k2] = C['rows'][i][k2], C['rows'][i][k1]
    return g


if MI:
    i0, i1, i2 = MI[0], MI[len(MI) // 2], MI[-1]
    s0 = base['rows'][i0]['s']
    T(f'matus row {i0}: s {s0} -> {s0 + 1}', mat_set(i0, 's', s0 + 1))
    T(f'matus row {i0}: s {s0} -> {s0 - 1}', mat_set(i0, 's', s0 - 1))
    T(f'matus row {i2}: s {base["rows"][i2]["s"]} -> 0', mat_set(i2, 's', 0))
    T(f'matus row {i1}: s {base["rows"][i1]["s"]} -> {base["rows"][i1]["s"] + 10}', mat_set(i1, 's', base['rows'][i1]['s'] + 10))
    T(f'matus row {i0}: swap a and b', mat_swap(i0, 'a', 'b'))
    T(f'matus row {i0}: swap c and d', mat_swap(i0, 'c', 'd'))
    T(f'matus row {i1}: swap a and c', mat_swap(i1, 'a', 'c'))
    T(f'matus row {i0}: multiplier negated', lambda C: C['rows'][i0].__setitem__('mult', str(-Fraction(C['rows'][i0]['mult']))))
    T(f'matus row {i1}: multiplier * 1001/1000', scale_mult(i1, Fraction(1001, 1000)))
    T(f'drop matus row {i2} (s={base["rows"][i2]["s"]})', drop_row(i2))
    T(f'matus row {i1}: drop last form of a', lambda C: C['rows'][i1].__setitem__('a', C['rows'][i1]['a'][:-1] or C['rows'][i1]['a']))
    T(f'matus row {i0}: replace d by x0', mat_set(i0, 'd', [[0, [1, 0]]]))
    T(f'INFO matus row {i0}: s {s0} -> {s0}.5 (float; check630 truncates, indep rejects)', mat_set(i0, 's', s0 + 0.5))



def run_one(t):
    name, C, inj = t
    path = os.path.join(TMP, f'neg_{abs(hash(name))}.json')
    json.dump(C, open(path, 'w'))
    if inj:
        r = subprocess.run([sys.executable, '-I', CHECK630, path], capture_output=True, text=True)
        c630 = 'PASS' if (r.returncode == 0 and 'PASS' in r.stdout) else 'FAIL'
    else:
        c630 = 'n/a'
    try:
        ok, info = indep_check.check(C, inj=inj, verbose=False)
        ind = 'PASS' if ok else 'FAIL'
    except SystemExit as e:
        ind, info = 'FAIL', str(e)
    except Exception as e:  # noqa: BLE001
        ind, info = 'FAIL', f'exception {type(e).__name__}: {e}'
    os.remove(path)
    return name, c630, ind, str(info)[:110]


with ThreadPoolExecutor(max_workers=int(sys.argv[2]) if len(sys.argv) > 2 else 12) as ex:
    res = list(ex.map(run_one, tests))
nbad = 0
for name, c630, ind, info in res:
    expect = 'PASS' if name.startswith('identity') else ('INFO' if name.startswith('INFO') else 'FAIL')
    flag = ''
    if expect != 'INFO' and ((c630 not in (expect, 'n/a')) or ind != expect):
        flag = '   <-- UNEXPECTED'
        nbad += 1
    print(f'{name:75s} check630={c630:4s} indep={ind:4s} {flag}')
    if ind == 'FAIL' and expect == 'FAIL':
        print(f'      indep: {info}')
print(f'unexpected outcomes: {nbad}')
