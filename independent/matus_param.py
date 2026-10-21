#!/usr/bin/env python3
"""Closed-form inductive certificate for the Matus family (as implemented in check630 / check3 'matus4'):
    M_s(a,b,c,d) = I(b;c|a) + s(I(a;b|c) + I(a;b|d) + I(c;d) - I(a;b)) + s(s+1)/2 (I(a;c|b) + I(a;b|c)).
Step s-1 -> s (s >= 2), with R a copy of A over (B,C) [(R,B,C) ~ (A,B,C), I(R; A D | B C) = 0]:
  M_s(A,B,C,D) = M_{s-1}(AR,BR,CR,D) + I(A;B|DR) + C(s+1,2)[I(A;R|B) + I(A;R|C)]
                 + s[I(A;R|BCD) + I(B;R|CD) + I(C;R|ABD) + I(D;R|A) + I(D;R|B)] + I(C;D|R) + s^2 I(D;R|ABC)
                 + eq(0) - (s+1) eq(B) - (s+1) eq(C) + (2s+1) eq(BC) - s(s+2) CI,
  where eq(T) = H(R T) - H(A T) (= 0 by the copy) and CI = I(R; AD | BC) (= 0).  All Shannon multipliers are >= 0.
The base case s = 1 (Zhang-Yeung) is the exact LP certificate of matus_lp.py.  The identity is verified exactly in
Fractions for every s in [2, SMAX]; since every coefficient is a polynomial of degree <= 2 in s, agreement at three
values already implies it for all s >= 2.  Usage: python -I matus_param.py SMAX"""
import sys
from fractions import Fraction
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
import matus_lp as ml

A, B, C, D, R = ml.A, ml.B, ml.Cv, ml.Dv, ml.R
I, H, add, M = ml.I, ml.H, ml.add, ml.M


def step_identity(s):
    s = Fraction(s)
    cc = s * (s + 1) / 2
    rhs = add((1, M(int(s) - 1, A | R, B | R, C | R, D)),
              (1, I(A, B, D | R)), (cc, I(A, R, B)), (cc, I(A, R, C)),
              (s, I(A, R, B | C | D)), (s, I(B, R, C | D)), (s, I(C, R, A | B | D)), (s, I(D, R, A)), (s, I(D, R, B)),
              (1, I(C, D, R)), (s * s, I(D, R, A | B | C)),
              (1, add((1, H(R)), (-1, H(A)))),
              (-(s + 1), add((1, H(R | B)), (-1, H(A | B)))),
              (-(s + 1), add((1, H(R | C)), (-1, H(A | C)))),
              (2 * s + 1, add((1, H(R | B | C)), (-1, H(A | B | C)))),
              (-s * (s + 2), I(R, A | D, B | C)))
    lhs = M(int(s), A, B, C, D)
    return all(lhs[k] == rhs[k] for k in range(32))


if __name__ == '__main__':
    smax = int(sys.argv[1])
    base, msg = ml.solve(1)
    print('s=1 (Zhang-Yeung) exact certificate:', 'OK' if base is not None else msg)
    bad = [s for s in range(2, smax + 1) if not step_identity(s)]
    print(f'closed-form step identity verified exactly for s = 2..{smax}: {"ALL OK" if not bad else "FAILED at " + str(bad[:10])}')
