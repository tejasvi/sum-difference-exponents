import EntropyBounds.TwoSet.Common

/-!
# The fixed-constant reading without suprema

* `admissibleK_le_of_pair_ceiling`: a pair ceiling `|X − Y| ≤ |X + Y|^λ` (all finite `X, Y ⊆ ℤ`) bounds every
  exponent that is admissible with fixed constants: `AdmissibleK θ → θ ≤ 2 − 1/λ`.  No supremum is involved.
* `admissibleK_one`, `bddAbove_admissibleK`, `one_le_thetaK`: `θ = 1` is admissible (`A = {1, …, n}`, `B = {0}`) and
  the admissible exponents are bounded above (by `3/2`, from `|X − Y| ≤ |X| |Y| ≤ |X + Y|^2`), so `thetaK` is the
  supremum of a nonempty bounded set and `1 ≤ thetaK`.
-/

open Finset Pointwise

namespace EntropyBounds.TwoSet

open SumsDifferences SumsDifferences.MultiScale

/-- **Headline form**: a pair ceiling bounds every exponent admissible with fixed constants. -/
theorem admissibleK_le_of_pair_ceiling {lam : ℝ}
    (hpair : ∀ X Y : Finset ℤ, (#(X - Y) : ℝ) ≤ (#(X + Y) : ℝ) ^ lam) {θ : ℝ} (h : AdmissibleK θ) :
    θ ≤ 2 - 1 / lam :=
  admissibleK_le (one_le_of_pair_ceiling hpair) hpair h

/-- `θ = 1` is admissible with `K = c = 1`: `A = {1, …, n₀}`, `B = {0}`. -/
theorem admissibleK_one : AdmissibleK 1 := by
  refine ⟨1, one_pos, 1, one_pos, fun n₀ => ⟨Icc (1 : ℤ) n₀, {0}, ?_, singleton_nonempty 0, ?_, ?_⟩⟩
  · simp
  · have e : Icc (1 : ℤ) n₀ + {0} = Icc (1 : ℤ) n₀ := by
      rw [add_singleton]; ext x; simp
    rw [e, one_mul]
  · have e1 : Icc (1 : ℤ) n₀ + {0} = Icc (1 : ℤ) n₀ := by
      rw [add_singleton]; ext x; simp
    have e2 : Icc (1 : ℤ) n₀ - {0} = Icc (1 : ℤ) n₀ := by
      ext x; simp
    rw [e1, e2, Real.rpow_one, one_mul]

/-- The trivial pair ceiling `|X − Y| ≤ |X| |Y| ≤ |X + Y|^2`. -/
theorem pair_ceiling_two (X Y : Finset ℤ) : (#(X - Y) : ℝ) ≤ (#(X + Y) : ℝ) ^ (2 : ℝ) := by
  rcases X.eq_empty_or_nonempty with rfl | hX
  · simp only [empty_sub, card_empty, Nat.cast_zero]; positivity
  rcases Y.eq_empty_or_nonempty with rfl | hY
  · simp only [sub_empty, card_empty, Nat.cast_zero]; positivity
  have h1 : #(X - Y) ≤ #X * #Y := card_sub_le
  have h2 : #X ≤ #(X + Y) := card_le_card_add_right hY
  have h3 : #Y ≤ #(X + Y) := card_le_card_add_left hX
  have h4 : #(X - Y) ≤ #(X + Y) * #(X + Y) := h1.trans (Nat.mul_le_mul h2 h3)
  rw [Real.rpow_two, sq]
  exact_mod_cast h4

/-- The admissible exponents are bounded above. -/
theorem bddAbove_admissibleK : BddAbove {t : ℝ | AdmissibleK t} :=
  ⟨2 - 1 / 2, fun _ ht => admissibleK_le_of_pair_ceiling pair_ceiling_two ht⟩

/-- **Non-vacuity**: `1 ≤ thetaK`. -/
theorem one_le_thetaK : 1 ≤ thetaK := le_csSup bddAbove_admissibleK admissibleK_one

end EntropyBounds.TwoSet
