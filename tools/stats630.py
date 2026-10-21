#!/usr/bin/env python3
"""Count the distinct closed sets that a certificate of Section 3 uses (the row "Closed sets used" of Table 1).

Usage: python3 tools/stats630.py checker/check630.py certs/NAME.json

The script reads the checker, adds in memory one line that prints the number of distinct closed sets H(cl F) the
checker has computed, and runs it on the certificate. The checker file itself is not modified.
"""
import sys, types

if not __debug__:
    raise SystemExit("this script relies on assert statements; run it without -O")

src = open(sys.argv[1]).read()
anchor = "    Ctot = sum(lam.values())"
assert src.count(anchor) == 1, 'the checker does not have the expected form'
src = src.replace(anchor, anchor + """
    flats = set(cache.values())
    print(f"closed sets used: {len(flats)}; classes after the identifications (EL): {len(set(find(F) for F in flats))}")""")
mod = types.ModuleType('check630_stats')
mod.__dict__['__name__'] = 'check630_stats'
exec(compile(src, 'check630_stats', 'exec'), mod.__dict__)
mod.main(sys.argv[2])
