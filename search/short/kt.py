"""Reproduce the Katz-Tao schemes (11/6 for R={0,1,inf}, 7/4 for R={0,1,2,inf}) with the entropy LP."""
import sys, time
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from eng import Config, Lattice, build_and_solve

X, Y, S, T = (1, 0), (0, 1), (1, 1), (1, 2)
R3 = [X, Y, S]
R4 = [X, Y, S, T]


def kt74():
    c = Config(R4)
    c.attach([0], [(0, X)])                 # g2: x = x(g1)
    c.attach([0, 1], [(0, T), (1, Y)])      # (g4, g3): x+2y(g4)=x+2y(g1), y(g3)=y(g2)
    return c


def kt116():
    c = Config(R3)
    c.attach([0], [(0, X)])                 # H1 = (g1, g2), x equal
    c.attach([0, 1], [(0, Y), (1, Y)])      # H0 = (g4, g3) glued along y's
    c.attach([0, 1], [(0, S), (1, Y)])      # H2 = (g6, g5) glued along (x+y of g1, y of g2)
    return c


if __name__ == '__main__':
    for name, fn in [('KT 7/4', kt74), ('KT 11/6', kt116)]:
        t0 = time.time()
        cfg = fn()
        print(name, 'vertices', cfg.n, 'relations', len(cfg.rels))
        lat = Lattice(cfg)
        res = build_and_solve(cfg, lat)
        print(name, 'LP value', res['value'], 'status', res['status'], f'{time.time()-t0:.1f}s')
        lam = [res['row_dual'][i] for i in res['bound_rows']]
        print('  bound duals', lam, 'sum', sum(lam))
