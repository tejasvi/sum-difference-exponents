import EntropyBounds.Iid.Ident

/-!
# Support bounds

If `Γ ⊆ X × Y`, then `x_a ∈ X` and `y_b ∈ Y` for all copies, so `x_a + y_b ∈ X + Y` and
`H(x_a + y_b) ≤ log #(X + Y)` (`HLm_bsumB`); also `H(x_a) ≤ log #(X + Y)` and `H(y_b) ≤ log #(X + Y)`
(`HLm_batomB`, since `#X, #Y ≤ #(X + Y)` for nonempty `X`, `Y`).
-/

open Finset Pointwise

namespace EntropyBounds.Iid

open SumsDifferences SumsDifferences.CoupledEntropy SumsDifferences.CoupledForms

variable {m : ℕ}

theorem HLm_single_le {Γ : Finset (ℤ × ℤ)} (hΓ : Γ.Nonempty) (f : Form m) {t : Finset ℤ}
    (ht : ∀ q ∈ Om Γ m, fval f q ∈ t) : HLm Γ m [f] ≤ Real.log #t := by
  rw [HLm_single_eq]
  exact pushEntropy_le_log_card (wt_nonneg Γ m) (wt_sum hΓ m) ht

/-- `H(x_a + y_b) ≤ log #(X + Y)`. -/
theorem HLm_bsumB {Γ : Finset (ℤ × ℤ)} (hΓ : Γ.Nonempty) {X Y : Finset ℤ} (hXY : Γ ⊆ X ×ˢ Y)
    (f : Form m) (a b : Fin m) (h : eqF f (addF (xF a) (yF b)) = true) :
    HLm Γ m [f] ≤ Real.log #(X + Y) := by
  rw [eqF_iff.mp h]
  refine HLm_single_le hΓ _ fun q hq => ?_
  rw [fval_addF, fval_xF, fval_yF]
  have ha := Finset.mem_product.mp (hXY (mem_Om.mp hq a))
  have hb := Finset.mem_product.mp (hXY (mem_Om.mp hq b))
  exact Finset.add_mem_add ha.1 hb.2

/-- `H(x_a) ≤ log #(X + Y)` and `H(y_b) ≤ log #(X + Y)`. -/
theorem HLm_batomB {Γ : Finset (ℤ × ℤ)} (hΓ : Γ.Nonempty) {X Y : Finset ℤ} (hXY : Γ ⊆ X ×ˢ Y)
    (f : Form m) (a : Fin m) (h : eqF f (xF a) = true || eqF f (yF a) = true) :
    HLm Γ m [f] ≤ Real.log #(X + Y) := by
  obtain ⟨p, hp⟩ := hΓ
  have hp' := Finset.mem_product.mp (hXY hp)
  have hXn : X.Nonempty := ⟨p.1, hp'.1⟩
  have hYn : Y.Nonempty := ⟨p.2, hp'.2⟩
  have hX : (#X : ℝ) ≤ #(X + Y) := by exact_mod_cast Finset.card_le_card_add_right hYn
  have hY : (#Y : ℝ) ≤ #(X + Y) := by exact_mod_cast Finset.card_le_card_add_left hXn
  have hX0 : (0 : ℝ) < #X := by exact_mod_cast hXn.card_pos
  have hY0 : (0 : ℝ) < #Y := by exact_mod_cast hYn.card_pos
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · rw [eqF_iff.mp h]
    refine (HLm_single_le ⟨p, hp⟩ _ (t := X) fun q hq => ?_).trans (Real.log_le_log hX0 hX)
    rw [fval_xF]
    exact (Finset.mem_product.mp (hXY (mem_Om.mp hq a))).1
  · rw [eqF_iff.mp h]
    refine (HLm_single_le ⟨p, hp⟩ _ (t := Y) fun q hq => ?_).trans (Real.log_le_log hY0 hY)
    rw [fval_yF]
    exact (Finset.mem_product.mp (hXY (mem_Om.mp hq a))).2

end EntropyBounds.Iid
