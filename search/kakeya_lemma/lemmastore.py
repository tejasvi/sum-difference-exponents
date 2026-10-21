"""Generic lemma records (four-variable inequalities with copy-lemma proofs) for certificates (check630.py
"lemma" rows).  DFZ entries come from dfz/lemmas.json (proofs by dfzlemma.py)."""
import json, os
from dfzlemma import target_dict

HERE = os.path.dirname(os.path.abspath(__file__))
_DFZ = None


def dfz_generic(k):
    global _DFZ
    if _DFZ is None:
        _DFZ = json.load(open(os.path.join(HERE, 'dfz', 'lemmas.json')))
    L = _DFZ[str(k)]
    coef = {''.join(sorted(S)): int(v) for S, v in target_dict(L['w']).items()}
    return dict(base='abcd', vars=L['vars'], steps=L['steps'], coef=coef, proof=L['proof'],
                source=f"DFZ (arXiv:1104.3602) Sec. VIII entry {k}, w = {L['w']}, steps {L['raw']}")

_ML = None


def matus_generic(s):
    global _ML
    if _ML is None:
        _ML = json.load(open(os.path.join(HERE, 'dfz', 'matus_lemmas.json')))
    return _ML[f'matus{int(s)}']


def get_lemma(lid, registry=None):
    if lid.startswith('dfz'):
        return dfz_generic(int(lid[3:]))
    if lid.startswith('matus'):
        return matus_generic(int(lid[5:]))
    return registry[lid]


def closure_ordered(ids, registry=None):
    """Lemma records for ids and everything their proofs apply, dependencies first."""
    order, seen = [], set()

    def visit(lid):
        if lid in seen:
            return
        seen.add(lid)
        L = get_lemma(lid, registry)
        for item in L['proof']:
            if item[0] == 'apply':
                visit(str(item[1]))
        order.append((lid, L))
    for lid in ids:
        visit(lid)
    return dict(order)
