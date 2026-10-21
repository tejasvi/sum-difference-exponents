#!/usr/bin/env python3
"""Lean proofs of the "lemmas" of a check630.py certificate (linear entropy inequalities proved by copy steps).

Used by tools/export_glue.py; can also be run alone:
    python3 -I tools/export_lemmas.py CERT.json NAME
which writes EntropyBounds/Lemma/Certs/NAME/Lemmas.lean.

Every lemma becomes a theorem `lem_<id>` stating `0 ≤ Σ_S coef_S X.H S` (S ⊆ the base letters 0..3) for every value
type `G`, every finite weighted space and every family `X : LSp G NL` of letters (`EntropyBounds/Lemma/Basic.lean`).
The proof follows the certificate: the copy steps are `LSp.copy` (a copied group of letters becomes one copied letter
per member), every proof entry becomes a fact about the final space (Shannon `H_sub`/`H_mono'`, `H_copy_eqlaw`,
`H_copy_ci`, earlier lemmas applied to joint variables via `joint`/`H_joint`), facts about earlier spaces are lifted
with `H_copy_old`, and the conclusion is an exact `linear_combination`.  check630.py verifies each lemma first.
"""
import sys, os, json, io, contextlib
from fractions import Fraction as Fr

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "ref"))
import check630  # noqa: E402

ROOT = os.path.dirname(HERE)

HEADER = """set_option linter.unusedVariables false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
"""


def fr_lean(x):
    x = Fr(x)
    if x.denominator == 1:
        return "(%d : ℝ)" % x.numerator
    return "((%d : ℝ) / %d)" % (x.numerator, x.denominator)


def fs(S, NL):
    S = sorted(S)
    if not S:
        return "(∅ : Finset (Fin %d))" % NL
    return "({%s} : Finset (Fin %d))" % (", ".join(str(x) for x in S), NL)


class LemmaInfo:
    """internal letters of one lemma."""

    def __init__(self, lid, L):
        self.lid = lid
        self.L = L
        base, letters = L['base'], L['vars']
        assert list(base) == list("abcd")[:len(base)] or len(base) == 4
        self.base = list(base)
        self.imap = {}          # certificate letter -> list of internal indices
        for k, x in enumerate(self.base):
            self.imap[x] = [k]
        nxt = len(self.base)
        self.steps = []         # dicts: src (internal -> internal), ov (set), nw (set), old (set), newl (letters)
        for st in L['steps']:
            old = set(i for x in self.imap for i in self.imap[x])
            src = {}
            nwset = set()
            for y, g in zip(st['new'], st['src']):
                ids = []
                for z in g:
                    for w in self.imap[z]:
                        src[nxt] = w
                        ids.append(nxt)
                        nwset.add(nxt)
                        nxt += 1
                self.imap[y] = ids
            ov = set(i for z in st['over'] for i in self.imap[z])
            self.steps.append(dict(src=src, ov=ov, nw=nwset, old=old, new=list(st['new']), srcs=list(st['src']),
                                   over=st['over']))
        self.n = nxt
        self.coef = {}
        for k, v in L['coef'].items():
            S = frozenset(i for x in k for i in self.imap[x])
            self.coef[S] = self.coef.get(S, Fr(0)) + Fr(v)

    def iset(self, letters):
        return frozenset(i for x in letters for i in self.imap[x])


def topo(lemmas):
    order, seen = [], set()

    def visit(lid, stack):
        if lid in seen:
            return
        assert lid not in stack, "cyclic lemmas"
        stack.add(lid)
        for it in lemmas[lid]['proof']:
            if it[0] == 'apply':
                visit(str(it[1]), stack)
        stack.discard(lid)
        seen.add(lid)
        order.append(lid)
    for lid in lemmas:
        visit(lid, set())
    return order


def lemma_text(info, infos, NL, pre):
    """Lean text for one lemma (definitions of its steps and the theorem)."""
    lid = info.lid
    nm = pre + lid
    T = len(info.steps)
    out = []
    tv = "{G : Type} [DecidableEq G] [Zero G]"
    for t, st in enumerate(info.steps):
        tbl = ", ".join("some %d" % st['src'][k] if k in st['src'] else "none" for k in range(NL))
        out.append("def %s_src%d : Fin %d → Option (Fin %d) := ![%s]\n" % (nm, t, NL, NL, tbl))
        out.append("def %s_ov%d : Finset (Fin %d) := %s\n" % (nm, t, NL, fs(st['ov'], NL)))
    for t in range(T):
        prev = "X" if t == 0 else "%s_X%d X" % (nm, t)
        out.append("noncomputable abbrev %s_X%d %s (X : LSp G %d) : LSp G %d := (%s).copy %s_src%d %s_ov%d\n"
                   % (nm, t + 1, tv, NL, NL, prev, nm, t, nm, t))
    Xn = lambda t: "X" if t == 0 else "(%s_X%d X)" % (nm, t)
    XF = Xn(T)
    stmt_terms = " + ".join("%s * X.H %s" % (fr_lean(c), fs(S, NL)) for S, c in sorted(info.coef.items(), key=lambda kv: sorted(kv[0])) if c != 0)
    lines = []
    for t in range(T):
        lines.append("  have hX%d : %s.Valid := LSp.valid_copy %s %s_src%d %s_ov%d"
                     % (t + 1, Xn(t + 1), "hX" if t == 0 else "hX%d" % t, nm, t, nm, t))
    hXn = lambda t: "hX" if t == 0 else "hX%d" % t
    # lifting: XF.H S = X_t.H S (S has no copies in steps t..T-1)
    def lift(S, t):
        """expression proving XF.H S = X_t.H S."""
        if t == T:
            return None
        parts = []
        for j in reversed(range(t, T)):
            parts.append("(LSp.H_copy_old (src := %s_src%d) (ov := %s_ov%d) %s %s (by decide))"
                         % (nm, j, nm, j, hXn(j), fs(S, NL)))
        e = parts[-1]
        for q in reversed(parts[:-1]):
            e = "(%s.trans %s)" % (q, e)
        return e
    facts = []      # (hyp name, coefficient for linear_combination)
    tot = {}        # atom (frozenset) -> coefficient of the combination (rhs - lhs), final-space atoms

    def addt(S, c):
        tot[S] = tot.get(S, Fr(0)) + c
    allv = info.iset(info.L['vars'])
    k = 0
    for item in info.L['proof']:
        kind, m = item[0], Fr(item[-1])
        hn = "e%d" % k
        k += 1
        if kind == 'sub':
            x, y, K = item[1], item[2], item[3]
            Ks = info.iset(K)
            S, Tt = Ks | info.iset(x), Ks | info.iset(y)
            U, V = S | Tt, S & Tt
            lines.append("  have %s := LSp.H_sub %s (S := %s) (T := %s) (U := %s) (V := %s) (by decide) (by decide)"
                         % (hn, hXn(T), fs(S, NL), fs(Tt, NL), fs(U, NL), fs(V, NL)))
            facts.append((hn, m))
            for A_, c in ((S, m), (Tt, m), (U, -m), (V, -m)):
                addt(A_, c)
        elif kind == 'mono':
            x = item[1]
            S = allv - info.iset(x)
            lines.append("  have %s := LSp.H_mono' %s (S := %s) (T := %s) (by decide)"
                         % (hn, hXn(T), fs(S, NL), fs(allv, NL)))
            facts.append((hn, m))
            addt(allv, m)
            addt(S, -m)
        elif kind == 'eqlaw':
            t, Sl = int(item[1]), item[2]
            st = info.steps[t]
            S = info.iset(Sl)
            img = set()
            for z in Sl:
                if z in st['new']:
                    img |= set(info.iset(st['srcs'][st['new'].index(z)]))
                else:
                    img |= set(info.imap[z])
            img = frozenset(img)
            # (X_{t+1}).H S = X_t.H img, lifted to XF
            l1, l2 = lift(S, t + 1), lift(img, t)
            core = ("LSp.H_copy_eqlaw (src := %s_src%d) (ov := %s_ov%d) %s %s %s (by decide) (by decide) (by decide)"
                    % (nm, t, nm, t, hXn(t), fs(S, NL), fs(img, NL)))
            lines.append("  have %s : %s.H %s = %s.H %s := by\n    rw [%s%s]\n    exact %s"
                         % (hn, XF, fs(S, NL), XF, fs(img, NL),
                            (l1 + ", ") if l1 else "", l2 if l2 else "", core)
                         if (l1 or l2) else
                         "  have %s : %s.H %s = %s.H %s := %s" % (hn, XF, fs(S, NL), XF, fs(img, NL), core))
            # check630: + m H(S) - m H(img); fact rhs - lhs = H(img) - H(S)
            facts.append((hn, -m))
            addt(img, -m)
            addt(S, m)
        elif kind == 'ci':
            t = int(item[1])
            st = info.steps[t]
            old, nw, ov = frozenset(st['old']), frozenset(st['nw']), frozenset(st['ov'])
            A1, A2, A3, A4 = old | nw, ov, old, nw | ov
            core = ("LSp.H_copy_ci' (src := %s_src%d) (ov := %s_ov%d) %s %s %s %s %s (by decide) (by decide) (by decide)"
                    " (by decide) (by decide)" % (nm, t, nm, t, hXn(t), fs(old, NL), fs(nw, NL), fs(A1, NL), fs(A4, NL)))
            lifts = [lift(A_, t + 1) for A_ in (A1, A2, A3, A4)]
            lifts = [x for x in lifts if x]
            stmt = "%s.H %s + %s.H %s = %s.H %s + %s.H %s" % (XF, fs(A1, NL), XF, fs(A2, NL), XF, fs(A3, NL), XF, fs(A4, NL))
            if lifts:
                lines.append("  have %s : %s := by\n    rw [%s]\n    exact %s" % (hn, stmt, ", ".join(lifts), core))
            else:
                lines.append("  have %s : %s := %s" % (hn, stmt, core))
            facts.append((hn, m))
            for A_, c in ((A3, m), (A4, m), (A1, -m), (A2, -m)):
                addt(A_, c)
        elif kind == 'apply':
            sub = infos[str(item[1])]
            args = item[2]
            A = [info.iset(a) for a in args] + [frozenset()] * (NL - len(args))
            Al = "![%s]" % ", ".join(fs(a, NL) for a in A)
            lines.append("  have %s := %s%s (%s.joint %s) (LSp.valid_joint %s %s)"
                         % (hn, pre, sub.lid, XF, Al, hXn(T), Al))
            rws = []
            for Ts, c in sorted(sub.coef.items(), key=lambda kv: sorted(kv[0])):
                if c == 0:
                    continue
                U = frozenset(i for j in Ts for i in A[j])
                rws.append("LSp.H_joint %s %s %s %s (by decide)" % (hXn(T), Al, fs(Ts, NL), fs(U, NL)))
                addt(U, m * c)
            if rws:
                lines.append("  rw [%s] at %s" % (", ".join(rws), hn))
            facts.append((hn, m))
        else:
            raise ValueError(kind)
    # empty-set atom
    e0 = tot.pop(frozenset(), Fr(0))
    lines.append("  have hE := LSp.H_empty' %s" % hXn(T))
    if e0 != 0:
        facts.append(("hE", e0))
    # check: tot == coef on base subsets, 0 elsewhere
    keys = set(tot) | set(info.coef)
    bad = [S for S in keys if tot.get(S, Fr(0)) != info.coef.get(S, Fr(0))]
    assert not bad, ("lemma %s: proof does not sum to the statement" % lid, bad[:3])
    # rewrite the goal's X.H S into XF.H S
    gl = [lift(S, 0) for S in info.coef if info.coef[S] != 0]
    gl = [x for x in gl if x]
    comb = " + ".join("%s * %s" % (fr_lean(c), h) for h, c in facts if c != 0)
    proof = "\n".join(lines)
    if gl:
        proof += "\n  rw [%s]" % ", ".join("← " + x for x in gl)
    proof += "\n  linear_combination %s\n" % comb
    out.append("/-- Certificate lemma `%s`. -/\ntheorem %s%s %s (X : LSp G %d) (hX : X.Valid) :\n    0 ≤ %s := by\n%s"
               % (lid, pre, lid, tv, NL, stmt_terms, proof))
    return "\n".join(out)


def build(C, pre="lem_"):
    """verify with check630 and return (NL, ordered infos, Lean text of all lemmas)."""
    lemmas = C.get('lemmas', {})
    # check630 verification of every lemma
    cache = {}

    def lookup(lid, depth):
        if lid in cache:
            return cache[lid]
        cache[lid] = check630.verify_lemma(lemmas[lid], lookup, depth)
        return cache[lid]
    for lid in lemmas:
        lookup(lid, 0)
    order = topo(lemmas)
    infos = {lid: LemmaInfo(lid, lemmas[lid]) for lid in order}
    NL = max([4] + [inf.n for inf in infos.values()])
    texts = [lemma_text(infos[lid], infos, NL, pre) for lid in order]
    return NL, infos, order, texts


def write(C, name, cert_path):
    NL, infos, order, texts = build(C)
    base = os.path.join(ROOT, "EntropyBounds", "Lemma", "Certs", name)
    os.makedirs(base, exist_ok=True)
    ns = "EntropyBounds.Lemma.Certs.%s" % name
    txt = ["import EntropyBounds.Lemma.Basic\n", HEADER,
           "/-! The lemmas of `%s` (generated by tools/export_lemmas.py): each is proved from its copy steps. -/\n"
           % os.path.basename(cert_path),
           "namespace %s\n" % ns, "open EntropyBounds.Lem\n"] + texts + ["end %s\n" % ns]
    open(os.path.join(base, "Lemmas.lean"), "w").write("\n".join(txt))
    print("wrote %s/Lemmas.lean: %d lemmas, NL = %d" % (base, len(order), NL))
    return NL, infos


if __name__ == "__main__":
    C = json.load(open(sys.argv[1]))
    write(C, sys.argv[2], sys.argv[1])
