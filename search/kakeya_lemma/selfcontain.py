"""Rewrite a certificate so that every non-Shannon row is a "lemma" row proved inside the certificate:
"matus" rows (s, a, b, c, d) become lemma rows matus<s> with the induction chain matus1..matus<max s>
(dfz/matus_lemmas.json).  The constant and all other rows are unchanged.  python selfcontain.py IN OUT"""
import sys, json, os

HERE = os.path.dirname(os.path.abspath(__file__))
src, dst = sys.argv[1:3]
C = json.load(open(src))
ML = json.load(open(os.path.join(HERE, 'dfz', 'matus_lemmas.json')))
rows, smax = [], 0
for r in C['rows']:
    if r['type'] == 'matus':
        s = int(r['s'])
        smax = max(smax, s)
        rows.append(dict(type='lemma', lemma=f'matus{s}', args=[r['a'], r['b'], r['c'], r['d']], mult=r['mult']))
    else:
        rows.append(r)
lemmas = {f'matus{s}': ML[f'matus{s}'] for s in range(1, smax + 1)}
lemmas.update(C.get('lemmas', {}))
C['rows'] = rows
C['lemmas'] = lemmas
json.dump(C, open(dst, 'w'))
print(f'{dst}: {sum(1 for r in rows if r["type"] == "lemma")} lemma rows, {len(lemmas)} lemmas (Matus chain to s = {smax})')
