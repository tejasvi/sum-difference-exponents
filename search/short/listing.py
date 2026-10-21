"""Grouped, human-readable listing of a lattice-row certificate (latrows.py output .json + .pkl).
usage: python listing.py CERT.json FORMS.json"""
import sys, json, pickle, itertools
from fractions import Fraction
from math import lcm
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from eng import Lattice
from kt import kt116

FREE = ['x0', 'y0', 'y1', 'x2', 'x4']
# ambient index -> vector over FREE
AMB = {0: (1, 0, 0, 0, 0), 1: (0, 1, 0, 0, 0), 2: (1, 0, 0, 0, 0), 3: (0, 0, 1, 0, 0), 4: (0, 0, 0, 1, 0),
       5: (0, 1, 0, 0, 0), 6: (0, 0, 0, 1, 0), 7: (0, 0, 1, 0, 0), 8: (0, 0, 0, 0, 1), 9: (1, 1, 0, 0, -1),
       10: (0, 0, 0, 0, 1), 11: (0, 0, 1, 0, 0)}


def amb_to_free(f):
    v = [0] * 5
    for i, a in enumerate(f):
        if a:
            for k in range(5):
                v[k] += a * AMB[i][k]
    return tuple(v)


def std_to_free(vtx, s):
    f = [0] * 12
    f[2 * vtx] = s[0]
    f[2 * vtx + 1] = s[1]
    return amb_to_free(f)


def name(v):
    # normalize sign: first nonzero positive
    nz = [a for a in v if a]
    if nz and nz[0] < 0:
        v = tuple(-a for a in v)
    out = ''
    for a, n in zip(v, FREE):
        if a == 0:
            continue
        if a == 1:
            out += ('+' if out else '') + n
        elif a == -1:
            out += '-' + n
        else:
            out += ('%+d' % a if out else '%d' % a) + n
    return out


def main(cpath, fpath):
    C = json.load(open(cpath))
    P = pickle.load(open(cpath.replace('.json', '.pkl'), 'rb'))
    forms = json.load(open(fpath))
    cfg = kt116()
    lat = Lattice(cfg, verbose=False, extra_amb=forms)
    assert lat.nflats == P['nflats']
    # free-coordinate vector of each ground element
    vec = {}
    for key, e in lat.idx.items():
        if key[0] == 'amb':
            v = amb_to_free(lat.extra_amb[key[1]])
        else:
            v = std_to_free(key[0], key[1])
        nz = [a for a in v if a]
        if nz[0] < 0:
            v = tuple(-a for a in v)
        cpx = sum(1 for a in v if a)
        if e not in vec or cpx < sum(1 for a in vec[e] if a):
            vec[e] = v
    def cpx(e):
        return (sum(abs(a) for a in vec[e]), e)
    def cl(es, base=0):
        f = base
        for e in es:
            f = int(lat.nxt[f, e])
        return f
    gcache = {}
    def gens(F, base=0):
        if (F, base) in gcache:
            return gcache[(F, base)]
        if F == base:
            return []
        mF, mb = lat.masks[F], lat.masks[base]
        els = sorted([e for e in range(lat.m) if (mF >> e) & 1 and not (mb >> e) & 1], key=cpx)
        for k in range(1, 6):
            best = None
            for S in itertools.combinations(els, k):
                if cl(S, base) == F:
                    sc = sum(cpx(e)[0] for e in S)
                    if best is None or sc < best[0]:
                        best = (sc, S)
            if best:
                gcache[(F, base)] = list(best[1])
                return gcache[(F, base)]
        raise RuntimeError('no generators')
    def nm(es):
        s = ', '.join(name(vec[e]) for e in es)
        return '(' + s + ')' if len(es) > 1 else s
    grouped = P['grouped']
    den = 1
    for g in grouped:
        den = lcm(den, Fraction(g['mult']).denominator)
    lam = {k: Fraction(v) for k, v in C['lambda'].items()}
    for v in lam.values():
        den = lcm(den, v.denominator)
    print(f"# certificate {cpath}: C = {C['claimed_C']} = {float(Fraction(C['claimed_C'])):.10f}")
    print(f"# weights scaled by {den}")
    print(f"#   lambda_X = {lam['1,0']*den}, lambda_Y = {lam['0,1']*den}, lambda_S = {lam['1,1']*den}  (/{den})")
    lines = []
    for g in grouped:
        w = Fraction(g['mult']) * den
        if g['kind'] == 'ci':
            lines.append((0, f"  {str(w):>8}  CI step {g['step']}"))
        elif g['kind'] == 'sm':
            M = g['M']
            a = gens(g['F'], M)
            b = gens(g['G'], M)
            c = gens(M) if M else []
            cond = (' | ' + ', '.join(name(vec[e]) for e in c)) if c else ''
            lines.append((len(c), f"  {str(w):>8}  I({nm(a)} ; {nm(b)}{cond})"))
        else:
            a = gens(g['F'], g['G'])
            c = gens(g['G'])
            lines.append((9, f"  {str(w):>8}  H({nm(a)} | {', '.join(name(vec[e]) for e in c)}) >= 0"))
    for _, l in sorted(lines, key=lambda t: t[0]):
        print(l)


if __name__ == '__main__':
    main(sys.argv[1], sys.argv[2])
