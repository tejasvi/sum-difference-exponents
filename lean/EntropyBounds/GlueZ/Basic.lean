import EntropyBounds.GlueG.NonShannon

/-!
# Witnesses with multiplier one, in every abelian group

`EntropyBounds.GlueG` checks determination witnesses whose multipliers `c` and `wc_k` are powers of two, and its
lemma `Conf.Det.gen` then needs that doubling is injective on `G`.  When every multiplier is `1` nothing is divided,
so the same determinations hold in every abelian group.  This file adds, without changing `EntropyBounds.GlueG`:

* `divG_one`: `divG 1 (1 • u) = u` in every abelian group;
* `checkDWR1`, `checkDWRs1`: the witness checks of `EntropyBounds.GlueG` with `c = 1` and `wc_k = 1` in place of
  `isPow2`;
* `Conf.Det.gen1`, `Conf.det_of_checkDWR1`, `Conf.det_of_checkDWRs1`, `Conf.H_eq_wit1`, `Conf.H_eq_zero_wit1`: the
  statements of `EntropyBounds.GlueG.Conf` for these checks, without a hypothesis on doubling;
* `HypZ`: the standing hypotheses `EntropyBounds.GlueG.Hyp` without the field `two`.
-/

open Finset

namespace EntropyBounds.GlueZ

open SumsDifferences SumsDifferences.CoupledEntropy SumsDifferences.CoupledForms EntropyBounds.Iid
  EntropyBounds.GlueG

variable {N : ℕ} {G : Type} [AddCommGroup G]

/-- `divG 1` inverts `1 •` in every abelian group. -/
theorem divG_one (u : G) : divG 1 ((1 : ℤ) • u) = u := by
  have hex : ∃ v : G, (1 : ℤ) • v = (1 : ℤ) • u := ⟨u, rfl⟩
  unfold divG
  rw [dite_eq_left hex]
  simpa using hex.choose_spec

/-- Check one witness for `f` from `l` modulo the relations `R`, with all multipliers equal to `1`. -/
def checkDWR1 (R l : List (Form N)) (f : Form N) (w : EntropyBounds.Glue.DWR N) : Bool :=
  (w.c == 1) && eqF (smulF w.c f) (addF (addF (lcF w.ms l) (lcF w.rs R)) w.g) &&
    (List.finRange N).all (fun k => ((w.g k).1 == 0 && (w.g k).2 == 0) ||
      ((w.wc k == 1) && eqF (addF (lcF (w.wit k) l) (lcF (w.wr k) R)) (smulF (w.wc k) (dform k))))

/-- Check witnesses for every form of `l₂` from `l₁`, with all multipliers equal to `1`. -/
def checkDWRs1 (R l₁ l₂ : List (Form N)) (ws : List (EntropyBounds.Glue.DWR N)) : Bool :=
  ws.length == l₂.length && (l₂.zip ws).all (fun p => checkDWR1 R l₁ p.1 p.2)

/-- The standing hypotheses without a hypothesis on doubling: distinct differences on the support `Γ`, a
probability weight. -/
structure HypZ (Γ : Finset (G × G)) (p : G × G → ℝ) : Prop where
  inj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q'
  nonneg : ∀ q ∈ Γ, 0 ≤ p q
  sum_one : ∑ q ∈ Γ, p q = 1

namespace Conf

open EntropyBounds.GlueG.Conf

variable [DecidableEq G] {C : EntropyBounds.GlueG.Conf N G}

/-- **Determination from integer data, modulo relations**, with all multipliers equal to `1` (every abelian
group). -/
theorem Det.gen1 {Γ : Finset (G × G)}
    (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q')
    (hmem : ∀ i ∈ C.Ω, ∀ v, C.co i v ∈ Γ) {R : List (Form N)} (hR : ∀ r ∈ R, C.Rel r)
    {l : List (Form N)} {f : Form N} (c : ℤ) (hc : c = 1) (ms rs : List ℤ) (g : Form N)
    (wc : Fin N → ℤ) (wit wr : Fin N → List ℤ)
    (hf : eqF (smulF c f) (addF (addF (lcF ms l) (lcF rs R)) g) = true)
    (hg : (List.finRange N).all (fun k => ((g k).1 == 0 && (g k).2 == 0) ||
      ((wc k == 1) && eqF (addF (lcF (wit k) l) (lcF (wr k) R)) (smulF (wc k) (dform k)))) = true) :
    C.Det l f := by
  rw [eqF_iff] at hf
  refine ⟨fun y => divG c (lcvG ms y + ∑ k, ((g k).1 • (rep Γ (divG (wc k) (lcvG (wit k) y))).1
      + (g k).2 • (rep Γ (divG (wc k) (lcvG (wit k) y))).2)), fun i hi => ?_⟩
  have hRz : lcvG rs (R.map fun r => rval r (C.co i)) = 0 := lcvG_zero _ _ (rel_vals hR hi)
  have key : ∀ k, (g k).1 • (rep Γ (divG (wc k) (lcvG (wit k) (l.map fun c => rval c (C.co i))))).1
      + (g k).2 • (rep Γ (divG (wc k) (lcvG (wit k) (l.map fun c => rval c (C.co i))))).2
      = (g k).1 • (C.co i k).1 + (g k).2 • (C.co i k).2 := by
    intro k
    have hk := List.all_eq_true.mp hg k (List.mem_finRange k)
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hk
    rcases hk with ⟨h1, h2'⟩ | ⟨hw0, hw⟩
    · rw [h1, h2']; simp
    · rw [eqF_iff] at hw
      have hd : divG (wc k) (lcvG (wit k) (l.map fun c => rval c (C.co i))) = (C.co i k).1 - (C.co i k).2 := by
        have := congrArg (fun h => rval h (C.co i)) hw
        simp only [rval_addF, rval_lcF, rval_smulF, rval_dform] at this
        rw [lcvG_zero (wr k) _ (rel_vals hR hi), add_zero] at this
        rw [this, hw0, divG_one]
      rw [hd, rep_eq hinj (hmem i hi k)]
  have hsum : lcvG ms (l.map fun c => rval c (C.co i)) + ∑ k, ((g k).1 • (rep Γ (divG (wc k) (lcvG (wit k)
      (l.map fun c => rval c (C.co i))))).1 + (g k).2 • (rep Γ (divG (wc k) (lcvG (wit k)
      (l.map fun c => rval c (C.co i))))).2) = c • rval f (C.co i) := by
    rw [Finset.sum_congr rfl fun k _ => key k, ← rval_lcF]
    have := congrArg (fun h => rval h (C.co i)) hf
    simp only [rval_smulF, rval_addF] at this
    rw [this, rval_lcF rs R, hRz, add_zero]
    rfl
  simp only
  rw [hsum, hc, divG_one]

variable {Γ : Finset (G × G)}

theorem det_of_checkDWR1
    (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') (hv : C.Valid Γ)
    {R : List (Form N)} (hR : ∀ r ∈ R, C.Rel r) {l : List (Form N)} {f : Form N} {w : EntropyBounds.Glue.DWR N}
    (h : checkDWR1 R l f w = true) : C.Det l f := by
  simp only [checkDWR1, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hc, hf⟩, hg⟩ := h
  exact Det.gen1 hinj hv.mem hR w.c hc w.ms w.rs w.g w.wc w.wit w.wr hf hg

theorem det_of_checkDWRs1
    (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') (hv : C.Valid Γ)
    {R : List (Form N)} (hR : ∀ r ∈ R, C.Rel r) {l₁ l₂ : List (Form N)} {ws : List (EntropyBounds.Glue.DWR N)}
    (h : checkDWRs1 R l₁ l₂ ws = true) : ∀ f ∈ l₂, C.Det l₁ f := by
  simp only [checkDWRs1, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hlen, hall⟩ := h
  intro f hf
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hf
  have hi' : i < ws.length := hlen ▸ hi
  have hmem : (l₂[i], ws[i]) ∈ l₂.zip ws := by
    rw [List.mem_iff_getElem]
    exact ⟨i, by simp [hi, hi'], by simp⟩
  exact det_of_checkDWR1 hinj hv hR (List.all_eq_true.mp hall _ hmem)

/-- **Identity from witnesses** with multiplier one. -/
theorem H_eq_wit1
    (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') (hv : C.Valid Γ)
    {R : List (Form N)} (hR : ∀ r ∈ R, C.Rel r) (l₁ l₂ : List (Form N)) (w₁₂ w₂₁ : List (EntropyBounds.Glue.DWR N))
    (h₁₂ : checkDWRs1 R l₁ l₂ w₁₂ = true) (h₂₁ : checkDWRs1 R l₂ l₁ w₂₁ = true) : C.H l₁ = C.H l₂ :=
  H_eq_of_det hv.nonneg (det_of_checkDWRs1 hinj hv hR h₁₂) (det_of_checkDWRs1 hinj hv hR h₂₁)

/-- `C.H l = 0` when every form of `l` is determined by the empty list, with multiplier one. -/
theorem H_eq_zero_wit1
    (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') (hv : C.Valid Γ)
    {R : List (Form N)} (hR : ∀ r ∈ R, C.Rel r) (l : List (Form N)) (w : List (EntropyBounds.Glue.DWR N))
    (h : checkDWRs1 R [] l w = true) : C.H l = 0 := by
  rw [← H_nil hv.nonneg hv.sum_one]
  exact H_eq_of_det hv.nonneg (fun f hf => absurd hf List.not_mem_nil) (det_of_checkDWRs1 hinj hv hR h)

end Conf

end EntropyBounds.GlueZ
