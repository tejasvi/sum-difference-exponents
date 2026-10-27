#!/usr/bin/env python3
"""Export a sum-difference entropy certificate (check630.py format) as Lean modules over every abelian group `G`:
EntropyBounds/GlueZ/Certs/NAME.

Usage: python3 -I tools/export_glue_z.py CERT.json NAME

tools/export_glue_g.py is imported and not modified.  It runs with its root moved to scratch/export_z/root, so nothing
is written under EntropyBounds/GlueG: closures and determination witnesses over Z[1/2], pool representatives, the
certificate first checked by tools/ref/check630.py, as for EntropyBounds/GlueG.  Then this script

* refuses unless every multiplier `c` and `wc` is 1.  The closures are then closures over Z and nothing is divided,
  so no hypothesis on 2-torsion is needed;
* rewrites the generated text for an arbitrary abelian group `G`: `HypZ` (no field `two`), the multiplier-one witness
  lemmas of EntropyBounds/GlueZ/Basic.lean (`Conf.det_of_checkDWR1`, `Conf.det_of_checkDWRs1`, `Conf.H_eq_wit1`,
  `Conf.H_eq_zero_wit1`, whose checks require `c = 1` and `wc = 1` again in the kernel), no hypothesis `h2` in the
  final theorems, namespace `EntropyBounds.GlueZ.Certs.NAME`.

Certificates with lemmas are refused (none of the GlueZ certificates has one).  An existing output directory or
scratch root is refused, never overwritten or removed.
"""
import sys, os, re

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import export_glue_g as egg  # noqa: E402  (unchanged)

ROOT = os.path.dirname(HERE)
ZROOT = os.path.join(ROOT, "scratch", "export_z", "root")

BANNED = [r"\bh\.two\b", r"x \+ x = 0", r"GlueG\.Certs", r"2-torsion", r"\bHyp\b", r"export_glue_g"]


def replace_all(txt, old, new, fn, need):
    n = txt.count(old)
    if need and n == 0:
        sys.exit("REFUSE: %s: expected text not found: %r" % (fn, old))
    return txt.replace(old, new)


def to_z(txt, fn, name):
    txt = replace_all(txt, "EntropyBounds.GlueG.Certs." + name, "EntropyBounds.GlueZ.Certs." + name, fn, True)
    if fn == "Defs.lean":
        txt = replace_all(txt, "import EntropyBounds.GlueG.SetForm\n",
                          "import EntropyBounds.GlueG.SetForm\nimport EntropyBounds.GlueZ.Basic\n", fn, True)
    txt = replace_all(txt, "open EntropyBounds.Iid EntropyBounds.GlueG ",
                      "open EntropyBounds.Iid EntropyBounds.GlueG EntropyBounds.GlueZ ", fn, True)
    txt = re.sub(r"\bHyp\b", "HypZ", txt)
    for lem in ("det_of_checkDWRs", "det_of_checkDWR", "H_eq_zero_wit", "H_eq_wit"):
        txt = txt.replace("Conf.%s h.two " % lem, "Conf.%s1 " % lem)
    txt = txt.replace("(h2 : ∀ x : G, x + x = 0 → x = 0) ", "")
    txt = txt.replace("⟨h2, hinj, hp, hs⟩", "⟨hinj, hp, hs⟩")
    txt = txt.replace("entropy_ineq Γ p h2 hinj hp hs", "entropy_ineq Γ p hinj hp hs")
    txt = txt.replace("set_ineq h2 A B P hP", "set_ineq A B P hP")
    txt = txt.replace("in an abelian group `G` without 2-torsion", "in every abelian group `G`")
    txt = txt.replace("tools/export_glue_g.py", "tools/export_glue_z.py")
    for pat in BANNED:
        m = re.search(pat, txt)
        if m:
            line = txt[:m.start()].count("\n") + 1
            sys.exit("REFUSE: %s line %d still matches %r" % (fn, line, pat))
    return txt


def main():
    cert, name = sys.argv[1], sys.argv[2]
    if not re.fullmatch(r"[A-Za-z0-9]+", name):
        sys.exit("REFUSE: bad name %r" % name)
    dst = os.path.join(ROOT, "EntropyBounds", "GlueZ", "Certs", name)
    if os.path.exists(dst):
        sys.exit("REFUSE: output directory exists: %s" % dst)
    if os.path.exists(ZROOT):
        sys.exit("REFUSE: scratch root exists (rename it first): %s" % ZROOT)
    os.makedirs(ZROOT)
    lem = os.path.join(ROOT, "EntropyBounds", "Glue", "Certs", name, "Lemmas.lean")
    if os.path.exists(lem):
        # export_glue_g.py compares a regenerated Lemmas module with the existing one under its root
        zlem = os.path.join(ZROOT, "EntropyBounds", "Glue", "Certs", name)
        os.makedirs(zlem)
        open(os.path.join(zlem, "Lemmas.lean"), "w", encoding="utf-8").write(open(lem, encoding="utf-8").read())
    egg.ROOT = ZROOT
    egg.SCRATCH = os.path.join(ZROOT, "scratch", "export_g")
    sys.argv = [sys.argv[0], cert, name]
    egg.main()
    bad = sorted(k for k in egg.STATS if k.split("=")[1] != "1")
    if bad:
        sys.exit("REFUSE: multipliers other than 1 (closures are not over Z): " +
                 ", ".join("%s x%d" % (k, egg.STATS[k]) for k in bad))
    src = os.path.join(ZROOT, "EntropyBounds", "GlueG", "Certs", name)
    files = sorted(os.listdir(src))
    if "Lemmas.lean" in files or os.path.exists(lem):
        sys.exit("REFUSE: certificates with lemmas are not supported")
    out = {fn: to_z(open(os.path.join(src, fn), encoding="utf-8").read(), fn, name) for fn in files}
    os.makedirs(dst)
    for fn in files:
        open(os.path.join(dst, fn), "w", encoding="utf-8").write(out[fn])
    print("multipliers:", sorted(egg.STATS.items()), "| wrote", dst, "(%d files)" % len(files))


if __name__ == "__main__":
    main()
