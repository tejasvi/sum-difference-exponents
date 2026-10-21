#!/usr/bin/env python3
"""Compare each dfz* lemma with DFZ (arXiv:1104.3602) Sec. VIII: parse the entry list (index) a b c d e f g h i spec),
check the certificate's 'source' entry number, w-vector and step string against the paper, and expand the template
  a I(A;B) <= b I(A;B|C) + c I(A;C|B) + d I(B;C|A) + e I(A;B|D) + f I(A;D|B) + g I(B;D|A) + h I(C;D) + i I(C;D|A)
into H-coefficients (as RHS - LHS >= 0) and compare with the lemma's coef dict.  Usage: dfz_paper_cmp.py CERT.json DFZ.txt"""
import json, re, sys
from fractions import Fraction
C = json.load(open(sys.argv[1])); txt = open(sys.argv[2]).read()
entries = {}
for line in txt.splitlines():
    parts = re.split(r'(?<!\S)(?=\d{1,3}\)\s+\d)', line)
    for ch in parts:
        m = re.match(r'(\d{1,3})\)\s+((?:\d+\s+){8}\d+)\s+(\S.*)$', ch.strip())
        if m:
            k = int(m.group(1)); w = [int(t) for t in m.group(2).split()]
            spec = m.group(3).strip()
            spec = re.match(r'^((?:[a-z()]+ [a-z()]+ [a-z]+\.)+)', spec.replace(' .', '.'))
            spec = spec.group(1) if spec else m.group(3).strip()
            entries.setdefault(k, (w, spec))
def H(sub):
    return frozenset(sub)
def I(coefs, c, X, Y, Z=''):
    for S, s in ((X + Z, 1), (Y + Z, 1), (X + Y + Z, -1), (Z, -1)):
        if S:
            key = H(S); coefs[key] = coefs.get(key, Fraction(0)) + c * s
def template(w):
    a, b, c, d, e, f, g, h, i = w
    co = {}
    I(co, -a, 'a', 'b'); I(co, b, 'a', 'b', 'c'); I(co, c, 'a', 'c', 'b'); I(co, d, 'b', 'c', 'a')
    I(co, e, 'a', 'b', 'd'); I(co, f, 'a', 'd', 'b'); I(co, g, 'b', 'd', 'a'); I(co, h, 'c', 'd'); I(co, i, 'c', 'd', 'a')
    return {k: v for k, v in co.items() if v}
def steps_str(L):
    out = []
    for st in L['steps']:
        src = ''.join(g if len(g) == 1 else f'({g})' for g in st['src'])
        out.append(f"{st['new']} {src} {st['over']}.")
    return ''.join(out)
print(f'parsed {len(entries)} DFZ Sec. VIII entries (max index {max(entries)})')
for lid, L in C['lemmas'].items():
    if not lid.startswith('dfz'):
        continue
    src = L.get('source', '')
    m = re.search(r'entry (\d+), w = \[([\d, ]+)\], steps (.*)$', src)
    k = int(m.group(1)); w = [int(t) for t in m.group(2).split(',')]; sspec = m.group(3).strip()
    pw, pspec = entries.get(k, (None, None))
    coefL = {frozenset(key): Fraction(v) for key, v in L['coef'].items()}
    coefT = template(w)
    print(f"{lid}: entry {k}: paper w {pw} | cert w {w} | match {pw == w}; paper steps '{pspec}' | cert source steps '{sspec}' | "
          f"lemma steps '{steps_str(L)}' | steps match {pspec == sspec == steps_str(L)}; template(w) == lemma coef: {coefT == coefL}")
    if coefT != coefL:
        diff = {''.join(sorted(S)): (coefT.get(S, 0), coefL.get(S, 0)) for S in set(coefT) | set(coefL) if coefT.get(S, 0) != coefL.get(S, 0)}
        print('    differences (template, lemma):', diff)
