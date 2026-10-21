"""Shannon rows of a check3 certificate as lattice-independent descriptors (warm start for colgen/rowgen).
Usage: python cert2descs.py CERT.json OUT.pkl"""
import sys, json, pickle
from fractions import Fraction
C = json.load(open(sys.argv[1]))
out = []
for r in C['rows']:
    if r['type'] == 'sub':
        out.append(('sub', int(r['copy']), tuple(tuple(str(Fraction(x)) for x in g) for g in r['K']),
                    (tuple(str(Fraction(x)) for x in r['i']), tuple(str(Fraction(x)) for x in r['j']))))
    elif r['type'] == 'mono':
        out.append(('mono', int(r['copy']), tuple(tuple(str(Fraction(x)) for x in g) for g in r['K']),
                    (tuple(str(Fraction(x)) for x in r['i']),)))
pickle.dump(out, open(sys.argv[2], 'wb'))
print(len(out), 'descriptors')
