import EntropyBounds.Glue.NonShannon

/-!
# From the entropy inequality to the set inequality (Tao's page 3b, `C_3b`)

If `H(X, Y) ≤ a H(X) + b H(Y) + c H(X + Y)` (`a, b, c ≥ 0`) for every finitely supported real pair whose
difference `x − y` is injective on the support, then for all finite `A, B ⊆ ℝ` and `G ⊆ A × B`,

  `|A −_G B| ≤ max(|A|, |B|, |A +_G B|)^(a + b + c)`,   `A ±_G B = {a ± b : (a, b) ∈ G}`

(`set_form`): choose one pair of `G` for each difference and take the uniform law on the chosen pairs.
-/

open Finset

namespace EntropyBounds.Glue

open SumsDifferences SumsDifferences.CoupledEntropy

theorem set_form {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hent : ∀ (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ), (∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') →
      (∀ q ∈ Γ, 0 ≤ p q) → ∑ q ∈ Γ, p q = 1 →
      pushEntropy Γ p (fun q => q) ≤ a * pushEntropy Γ p (fun q => q.1) + b * pushEntropy Γ p (fun q => q.2)
        + c * pushEntropy Γ p (fun q => q.1 + q.2))
    (A B : Finset ℝ) (G : Finset (ℝ × ℝ)) (hG : G ⊆ A ×ˢ B) :
    (#(G.image fun q => q.1 - q.2) : ℝ)
      ≤ (max (max (#A : ℝ) (#B : ℝ)) (#(G.image fun q => q.1 + q.2) : ℝ)) ^ (a + b + c) := by
  classical
  rcases G.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.image_empty, Finset.card_empty, Nat.cast_zero]
    positivity
  set D := G.image fun q => q.1 - q.2 with hDdef
  set S := G.image fun q => q.1 + q.2 with hSdef
  let sel : ℝ → ℝ × ℝ := fun z => if h : ∃ q ∈ G, q.1 - q.2 = z then h.choose else 0
  have hsel : ∀ z ∈ D, sel z ∈ G ∧ (sel z).1 - (sel z).2 = z := by
    intro z hz
    have h : ∃ q ∈ G, q.1 - q.2 = z := by
      obtain ⟨q, hq, hqz⟩ := Finset.mem_image.mp hz
      exact ⟨q, hq, hqz⟩
    simp only [sel, dif_pos h]
    exact h.choose_spec
  set G' := D.image sel with hG'def
  have hG'G : G' ⊆ G := by
    intro q hq
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hq
    exact (hsel z hz).1
  have hcard : #G' = #D := Finset.card_image_of_injOn fun z hz z' hz' h => by
    have h1 := (hsel z hz).2
    have h2 := (hsel z' hz').2
    rw [← h1, ← h2, h]
  have hinj' : ∀ q ∈ G', ∀ q' ∈ G', q.1 - q.2 = q'.1 - q'.2 → q = q' := by
    intro q hq q' hq' hd
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨z', hz', rfl⟩ := Finset.mem_image.mp hq'
    rw [(hsel z hz).2, (hsel z' hz').2] at hd
    rw [hd]
  have hG'ne : G'.Nonempty := (hne.image _).image _
  have hn : (0 : ℝ) < #G' := by exact_mod_cast hG'ne.card_pos
  set p : ℝ × ℝ → ℝ := fun _ => (#G' : ℝ)⁻¹ with hpdef
  have hp : ∀ q ∈ G', 0 ≤ p q := fun _ _ => by positivity
  have hs : ∑ q ∈ G', p q = 1 := by
    simp only [p, Finset.sum_const, nsmul_eq_mul]
    field_simp
  have h := hent G' p hinj' hp hs
  have hid : pushEntropy G' p (fun q => q) = Real.log #G' := by
    rw [pushEntropy_id_eq_entropy]
    exact entropy_uniform G'
  have hA : 0 < #A := by
    obtain ⟨q, hq⟩ := hne
    exact Finset.card_pos.mpr ⟨q.1, (Finset.mem_product.mp (hG hq)).1⟩
  have hB : 0 < #B := by
    obtain ⟨q, hq⟩ := hne
    exact Finset.card_pos.mpr ⟨q.2, (Finset.mem_product.mp (hG hq)).2⟩
  have hS : 0 < #S := (hne.image _).card_pos
  have hX : pushEntropy G' p (fun q => q.1) ≤ Real.log #A :=
    pushEntropy_le_log_card hp hs fun q hq => (Finset.mem_product.mp (hG (hG'G hq))).1
  have hY : pushEntropy G' p (fun q => q.2) ≤ Real.log #B :=
    pushEntropy_le_log_card hp hs fun q hq => (Finset.mem_product.mp (hG (hG'G hq))).2
  have hZ : pushEntropy G' p (fun q => q.1 + q.2) ≤ Real.log #S :=
    pushEntropy_le_log_card hp hs fun q hq => Finset.mem_image_of_mem _ (hG'G hq)
  set M : ℝ := max (max (#A : ℝ) (#B : ℝ)) (#S : ℝ) with hMdef
  have hAM : (#A : ℝ) ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
  have hBM : (#B : ℝ) ≤ M := le_trans (le_max_right _ _) (le_max_left _ _)
  have hSM : (#S : ℝ) ≤ M := le_max_right _ _
  have hA' : (0 : ℝ) < #A := by exact_mod_cast hA
  have hB' : (0 : ℝ) < #B := by exact_mod_cast hB
  have hS' : (0 : ℝ) < #S := by exact_mod_cast hS
  have hM0 : 0 < M := lt_of_lt_of_le hA' hAM
  have hlogA := Real.log_le_log hA' hAM
  have hlogB := Real.log_le_log hB' hBM
  have hlogS := Real.log_le_log hS' hSM
  have hlog : Real.log #D ≤ (a + b + c) * Real.log M := by
    rw [← hcard, ← hid]
    nlinarith [mul_le_mul_of_nonneg_left hlogA ha, mul_le_mul_of_nonneg_left hlogB hb,
      mul_le_mul_of_nonneg_left hlogS hc, mul_le_mul_of_nonneg_left hX ha, mul_le_mul_of_nonneg_left hY hb,
      mul_le_mul_of_nonneg_left hZ hc]
  have hD0 : (0 : ℝ) < #D := by rw [← hcard]; exact_mod_cast hG'ne.card_pos
  rw [← Real.exp_log hD0, Real.rpow_def_of_pos hM0, mul_comm (Real.log M)]
  exact Real.exp_le_exp.mpr hlog

end EntropyBounds.Glue
