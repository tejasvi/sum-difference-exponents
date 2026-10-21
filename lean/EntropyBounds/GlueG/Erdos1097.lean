import EntropyBounds.GlueG.Certs.CL3B6SC.Final

/-!
# Common differences of three-term progressions (Erdős Problem #1097)

For a finite set `A` in an abelian group without 2-torsion, let `D` be the set of nonzero `d` such that
`a, a + d, a + 2d ∈ A` for some `a`.  Then `|D| ≤ |A|^C` with `C` the exponent of the certificate `c3b_torsionfree.json`
(`ap_differences_card_le`); for a finite set of integers the number of positive such `d` is at most `|A|^C`
(`ap_differences_pos_card_le_int`).

Proof: choose `a_d` for each `d ∈ D` and let `P = {(a_d + 2d, a_d)} ⊆ A × A`.  Then `A −_P A = {2d : d ∈ D}` has `|D|`
elements (doubling is injective), and `A +_P A = {2(a_d + d)} ⊆ {2x : x ∈ A}` has at most `|A|` elements, so the max
form of the set inequality (`set_ineq'`) gives `|D| ≤ max(|A|, |A|, |A +_P A|)^C = |A|^C`.
-/

open Finset Pointwise

namespace EntropyBounds.GlueG.Certs.CL3B6SC

/-- The nonzero common differences of three-term progressions in `A`. -/
def apDiffs {G : Type} [AddCommGroup G] [DecidableEq G] (A : Finset G) : Finset G :=
  (A - A).filter (fun d => d ≠ 0 ∧ ∃ a ∈ A, a + d ∈ A ∧ a + d + d ∈ A)

/-- **Erdős #1097, the `|A|^C` bound** in an abelian group without 2-torsion. -/
theorem ap_differences_card_le {G : Type} [AddCommGroup G] [DecidableEq G] (h2 : ∀ x : G, x + x = 0 → x = 0)
    (A : Finset G) :
    (#(apDiffs A) : ℝ) ≤ (#A : ℝ) ^ (4785864240814563464816432634036471899 / 2619096017836492522862695316182077572 : ℝ) := by
  classical
  obtain ⟨D, hD⟩ : ∃ D, D = apDiffs A := ⟨_, rfl⟩
  rw [← hD]
  have hmem : ∀ d ∈ D, d ≠ 0 ∧ ∃ a ∈ A, a + d ∈ A ∧ a + d + d ∈ A := by
    intro d hd
    rw [hD, apDiffs, Finset.mem_filter] at hd
    exact hd.2
  -- a starting point for each difference
  have hex : ∀ d ∈ D, ∃ a, a ∈ A ∧ a + d ∈ A ∧ a + d + d ∈ A := by
    intro d hd
    obtain ⟨_, a, ha, h1, h3⟩ := hmem d hd
    exact ⟨a, ha, h1, h3⟩
  choose! st hst using hex
  -- doubling is injective
  have hdbl : ∀ x y : G, x + x = y + y → x = y := by
    intro x y hxy
    have := h2 (x - y) (by rw [show x - y + (x - y) = (x + x) - (y + y) by abel, hxy, sub_self])
    exact sub_eq_zero.mp this
  obtain ⟨P, hPdef⟩ : ∃ P : Finset (G × G), P = D.image (fun d => (st d + d + d, st d)) := ⟨_, rfl⟩
  have hPA : P ⊆ A ×ˢ A := by
    intro q hq
    rw [hPdef] at hq
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_product.mpr ⟨(hst d hd).2.2, (hst d hd).1⟩
  have hdiff : P.image (fun q => q.1 - q.2) = D.image (fun d => d + d) := by
    rw [hPdef, Finset.image_image]
    refine Finset.image_congr fun d _ => ?_
    simp only [Function.comp_apply]
    abel
  have hsum : P.image (fun q => q.1 + q.2) ⊆ A.image (fun x => x + x) := by
    intro z hz
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz
    rw [hPdef] at hq
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hq
    refine Finset.mem_image.mpr ⟨st d + d, (hst d hd).2.1, ?_⟩
    simp only
    abel
  have hcardD : #(P.image fun q => q.1 - q.2) = #D := by
    rw [hdiff]
    exact Finset.card_image_of_injOn fun x _ y _ h => hdbl x y h
  have hcardS : #(P.image fun q => q.1 + q.2) ≤ #A :=
    (Finset.card_le_card hsum).trans Finset.card_image_le
  have key := set_ineq' h2 A A P hPA
  rw [hcardD] at key
  refine key.trans (Real.rpow_le_rpow (by positivity) ?_ (by norm_num))
  rw [max_self]
  exact max_le le_rfl (by exact_mod_cast hcardS)

/-- **Erdős #1097 for integers**: the number of positive common differences of three-term progressions in a finite
set `A ⊆ ℤ` is at most `|A|^C`. -/
theorem ap_differences_pos_card_le_int (A : Finset ℤ) :
    (#((A - A).filter (fun d => 0 < d ∧ ∃ a ∈ A, a + d ∈ A ∧ a + 2 * d ∈ A)) : ℝ)
      ≤ (#A : ℝ) ^ (4785864240814563464816432634036471899 / 2619096017836492522862695316182077572 : ℝ) := by
  have hsub : (A - A).filter (fun d => 0 < d ∧ ∃ a ∈ A, a + d ∈ A ∧ a + 2 * d ∈ A) ⊆ apDiffs A := by
    intro d hd
    obtain ⟨hdA, hpos, a, ha, had, ha2d⟩ := Finset.mem_filter.mp hd
    rw [apDiffs, Finset.mem_filter]
    refine ⟨hdA, hpos.ne', a, ha, had, ?_⟩
    rwa [add_assoc, ← two_mul]
  have h := ap_differences_card_le (G := ℤ) (fun x hx => by omega) A
  exact le_trans (by exact_mod_cast Finset.card_le_card hsub) h

end EntropyBounds.GlueG.Certs.CL3B6SC
