#!/usr/bin/env python3
"""Matus chain audit of a cl3b6 certificate (own code, not the checker's).
(a) matus lemma ids contiguous 1..K; (b) coef of matus_k == expansion of
    M_k(a,b,c,d) = I(b;c|a) + k(I(a;b|c)+I(a;b|d)+I(c;d)-I(a;b)) + k(k+1)/2 (I(a;c|b)+I(a;b|c));
(c) chain: copy step r <- a over bc; matus1 has no 'apply'; matus_k (k>=2) applies only matus_{k-1} to (ar,br,cr,d);
(d) own expansion of each proof (sub = m I(x;y|K), m>=0; eqlaw = m (H(S) - H(phi S)); ci = m I(new; old|over);
    apply = m * coef of the applied lemma under the argument map, m>=0) sums exactly to coef.
Usage: matus_check.py CERT.json"""
import json, re, sys
from fractions import Fraction
C = json.load(open(sys.argv[1]))
Ls = C['lemmas']


def addI(co, c, X, Y, Z=''):
    for S, s in ((X + Z, 1), (Y + Z, 1), (X + Y + Z, -1), (Z, -1)):
        if S:
            k = frozenset(S)
            co[k] = co.get(k, Fraction(0)) + c * s


def M(k):
    co = {}
    addI(co, 1, 'b', 'c', 'a')
    for X, Y, Z, s in (('a', 'b', 'c', 1), ('a', 'b', 'd', 1), ('c', 'd', '', 1), ('a', 'b', '', -1)):
        addI(co, Fraction(k) * s, X, Y, Z)
    addI(co, Fraction(k * (k + 1), 2), 'a', 'c', 'b')
    addI(co, Fraction(k * (k + 1), 2), 'a', 'b', 'c')
    return {S: v for S, v in co.items() if v}


ids = sorted(int(m.group(1)) for k in Ls for m in [re.fullmatch(r'matus(\d+)', k)] if m)
print(f'matus lemmas: {len(ids)}, ids {ids[0]}..{ids[-1]}, contiguous {ids == list(range(1, len(ids) + 1))}')
bad = []
for k in ids:
    L = Ls[f'matus{k}']
    coef = {frozenset(S): Fraction(v) for S, v in L['coef'].items()}
    ok_coef = coef == M(k)
    ok_steps = L['base'] == 'abcd' and L['vars'] == 'abcdr' and L['steps'] == [{'new': 'r', 'src': ['a'], 'over': 'bc'}]
    applies = [it for it in L['proof'] if it[0] == 'apply']
    if k == 1:
        ok_chain = not applies
    else:
        ok_chain = (len(applies) == 1 and applies[0][1] == f'matus{k - 1}' and applies[0][2] == ['ar', 'br', 'cr', 'd']
                    and Fraction(applies[0][3]) == 1)
    tot = {}

    def add(S, c):
        S = frozenset(S)
        if S:
            tot[S] = tot.get(S, Fraction(0)) + c
    ok_rows = True
    old, new, over = set('abcd'), 'r', set('bc')
    for it in L['proof']:
        m = Fraction(it[-1])
        if it[0] == 'sub':
            x, y, K = it[1], it[2], it[3]
            ok_rows &= m >= 0 and len(x) == 1 and len(y) == 1 and x != y and x not in K and y not in K
            add(K + x, m); add(K + y, m); add(K + x + y, -m); add(K, -m)
        elif it[0] == 'eqlaw':
            S = it[2]
            ok_rows &= it[1] == 0 and 'r' in S and set(S) <= over | {'r'}
            add(S, m); add(S.replace('r', 'a'), -m)
        elif it[0] == 'ci':
            ok_rows &= it[1] == 0
            add(over | {new}, m); add(old, m); add(old | {new}, -m); add(over, -m)
        elif it[0] == 'apply':
            ok_rows &= m >= 0
            amap = dict(zip('abcd', it[2]))
            for S, cS in M(k - 1).items():
                add(set(x for y in S for x in amap[y]), m * cS)
        else:
            ok_rows = False
    tot = {S: v for S, v in tot.items() if v}
    ok_sum = tot == coef
    if not (ok_coef and ok_steps and ok_chain and ok_rows and ok_sum):
        bad.append(k)
    if k <= 3 or k == ids[-1] or k in bad:
        print(f'matus{k}: coef == M_k {ok_coef}; copy step r<-a over bc {ok_steps}; chain {ok_chain}; rows valid {ok_rows}; '
              f'own proof expansion == coef {ok_sum}')
print(f'ALL {len(ids)} matus lemmas pass (a)-(d): {not bad}; failing: {bad}')
