"""Configurations with conditional-copy vertices (two-set exponent), for rowgen.py / cert4.py.
Job keys: nD (iid D copies, default 2); steps: list of
    ["W", [i, j], name]                     independent W vertex with law mu^{*i} nu^{*j}
    ["C", [atom names], [given forms], [new names]]   conditional copy of the atoms given the forms
forms: explicit extra forms over the names (x0, y0, x1, y1, ..., then the step names);
gen: list of generated families with 'lead' names: "base3" (3-term +-1 combos of D coordinates),
    "L2f"/"L3f"/"L4f" (lead + all sign patterns on 2/3/4 D coordinates), "L1m" (lead - a).
Automorphisms: none (a conditional copy depending on one D copy breaks the D swap)."""
import re, itertools
from eng2 import Config2, F


def parse(s, names):
    d = {}
    for sign, var in re.findall(r'([+-]?)([a-z][0-9a-z]*)', s.replace(' ', '')):
        d[names[var]] = d.get(names[var], 0) + (-1 if sign == '-' else 1)
    return d


def build(job):
    c = Config2()
    c.fresh('D')
    nD = job.get('nD', 2)
    for k in range(nD - 1):
        c.copy([0, 1], [])
    names = {}
    for k in range(nD):
        names[f'x{k}'], names[f'y{k}'] = 2 * k, 2 * k + 1
    for st in job.get('steps', []):
        if st[0] == 'W':
            v = c.fresh('W', tuple(st[1]))
            names[st[2]] = c.vatoms[v][0]
        elif st[0] == 'C':
            atoms = [names[a] for a in st[1]]
            V = [F(c, parse(s, names)) for s in st[2]]
            new = c.copy(atoms, V)
            for nm, nc in zip(st[3], new):
                names[nm] = nc
        else:
            raise ValueError(st)
    dcoords = list(range(2 * nD))
    ex = []

    def combos(coords, nz, lead=None):
        out = []
        for S in itertools.combinations(coords, nz):
            for cs in itertools.product((1, -1), repeat=nz):
                if cs[0] < 0:
                    continue
                d = dict(zip(S, cs))
                if lead is not None:
                    d[lead] = 1
                out.append(F(c, d))
        return out
    leads = [names[n] for n in job.get('lead', [])]
    for spec in job.get('gen', []):
        if spec == 'base3':
            ex += combos(dcoords, 3)
        elif spec == 'base4':
            ex += combos(dcoords, 4)
        elif spec in ('L2f', 'L3f', 'L4f'):
            for w in leads:
                ex += combos(dcoords, int(spec[1]), lead=w)
        elif spec == 'L1m':
            for w in leads:
                ex += [F(c, {w: 1, a: -1}) for a in dcoords]
        else:
            raise ValueError(spec)
    for s in job.get('forms', []):
        ex.append(F(c, parse(s, names)))
    return c, ex, []
