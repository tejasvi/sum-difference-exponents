import EntropyBounds.Iid.Support
import EntropyBounds.Iid.Witness
import SumDifference.ThetaClosedFormBound

/-!
# Two-set exponent certificates: grid rows, the reflected pair, and the transfer

* `hg Γ i j = ent (P μ ν i j)`: the grid `h(i, j)` of a coupled pair, and its rows (Kleinwaks' Lemmas 4.2-4.3):
  concavity, monotonicity, the link `L + h(i,j) ≤ h(i+1,j) + h(i,j+1)`, `h(1,1) ≤ log #(X+Y)`.
* The reflected pair `mirror Γ ⊆ (-Y) × (-X)`: nonempty, distinct differences, same `L` and `S`, transposed grid.
* `pair_ceiling_of_cert`: a certificate inequality `log #Γ ≤ λ log #(X+Y)` for every coupling gives the pair ceiling
  `|X − Y| ≤ |X + Y|^λ` for all finite `X, Y ⊆ ℤ`; with Kleinwaks' transfer, `theta ≤ 2 − 1/λ`.
* `thetaK`: the constant of GGSTW Problem 6.44 / Tao's page 3a, where the implied constants are fixed along the
  sequence (`AdmissibleK`: some `K` and `c` work for arbitrarily large `A`), and `thetaK_le_of_pair_ceiling`:
  `thetaK ≤ 2 − 1/λ` (Kleinwaks' `theta` asks for every `K`, so the packaged transfer bounds a possibly smaller
  number; the multiscale inequality `card_sub_pow_le_multiscale` holds for every `K`).
-/

open Finset Pointwise

namespace EntropyBounds.TwoSet

open SumsDifferences SumsDifferences.CoupledEntropy SumsDifferences.CoupledForms EntropyBounds.Iid

/-! ## The grid -/

/-- `h(i, j) = H(μ^i ν^j)` for the marginals of `Γ`. -/
noncomputable def hg (Γ : Finset (ℤ × ℤ)) (i j : ℕ) : ℝ := ent (P (margFst Γ) (margSnd Γ) i j)

variable {Γ : Finset (ℤ × ℤ)}

theorem hg_concx (hΓ : Γ.Nonempty) (i j : ℕ) : 0 ≤ 2 * hg Γ (i + 1) j - hg Γ i j - hg Γ (i + 2) j := by
  have := (grid_concave (isLaw_margFst hΓ) (isLaw_margSnd hΓ) i j).1
  unfold hg; linarith

theorem hg_concy (hΓ : Γ.Nonempty) (i j : ℕ) : 0 ≤ 2 * hg Γ i (j + 1) - hg Γ i j - hg Γ i (j + 2) := by
  have := (grid_concave (isLaw_margFst hΓ) (isLaw_margSnd hΓ) i j).2.1
  unfold hg; linarith

theorem hg_monox (hΓ : Γ.Nonempty) (i j : ℕ) : 0 ≤ hg Γ (i + 1) j - hg Γ i j := by
  have := (grid_concave (isLaw_margFst hΓ) (isLaw_margSnd hΓ) i j).2.2.1
  unfold hg; linarith

theorem hg_monoy (hΓ : Γ.Nonempty) (i j : ℕ) : 0 ≤ hg Γ i (j + 1) - hg Γ i j := by
  have := (grid_concave (isLaw_margFst hΓ) (isLaw_margSnd hΓ) i j).2.2.2
  unfold hg; linarith

theorem hg_link (hΓ : Γ.Nonempty) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q')
    (i j : ℕ) : 0 ≤ hg Γ (i + 1) j + hg Γ i (j + 1) - hg Γ i j - Real.log #Γ := by
  have := link hΓ hinj i j
  unfold hg; linarith

theorem hg_h11 (hΓ : Γ.Nonempty) {X Y : Finset ℤ} (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ Real.log #(X + Y) - hg Γ 1 1 := by
  have := ent_mul_le_log_card (isLaw_margFst hΓ) (isLaw_margSnd hΓ) (support_margFst_subset hXY)
    (support_margSnd_subset hXY)
  have e : P (margFst Γ) (margSnd Γ) 1 1 = margFst Γ * margSnd Γ := by simp [P]
  unfold hg; rw [e]; linarith

theorem hg_h00 : hg Γ 0 0 = 0 := by
  have e : P (margFst Γ) (margSnd Γ) 0 0 = 1 := by simp [P]
  unfold hg ent entropy
  rw [e, AddMonoidAlgebra.support, AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single,
    Finsupp.support_single_ne_zero _ one_ne_zero]
  simp

theorem hg_nonneg (hΓ : Γ.Nonempty) (i j : ℕ) : 0 ≤ hg Γ i j :=
  ClosedForm.ent_nonneg_of_isLaw (isLaw_P (isLaw_margFst hΓ) (isLaw_margSnd hΓ) i j)

/-! ## The reflected pair -/

theorem mirror_nonempty (hΓ : Γ.Nonempty) : (mirror Γ).Nonempty := hΓ.image _

theorem mirror_inj (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    ∀ q ∈ mirror Γ, ∀ q' ∈ mirror Γ, q.1 - q.2 = q'.1 - q'.2 → q = q' := by
  intro q hq q' hq' hd
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hq'
  have : a = b := hinj a ha b hb (by simp only [neg_sub_neg] at hd; exact hd)
  rw [this]

theorem mirror_subset {X Y : Finset ℤ} (hXY : Γ ⊆ X ×ˢ Y) : mirror Γ ⊆ (-Y) ×ˢ (-X) := by
  intro q hq
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
  have := hXY ha
  rw [Finset.mem_product] at this ⊢
  exact ⟨Finset.neg_mem_neg this.2, Finset.neg_mem_neg this.1⟩

theorem log_card_mirror : Real.log #(mirror Γ) = Real.log #Γ := by rw [card_mirror]

theorem log_card_negsum (X Y : Finset ℤ) : Real.log #((-Y) + (-X)) = Real.log #(X + Y) := by
  rw [← neg_add, Finset.card_neg, add_comm]

theorem hg_mirror (i j : ℕ) : hg (mirror Γ) i j = hg Γ j i := ent_P_mirror Γ i j

/-! ## The transfer -/

/-- A certificate inequality for every coupling gives the pair ceiling. -/
theorem pair_ceiling_of_cert {lam : ℝ} (hlam : 0 ≤ lam)
    (hcert : ∀ (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ), Γ.Nonempty →
      (∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') → Γ ⊆ X ×ˢ Y →
      Real.log #Γ ≤ lam * Real.log #(X + Y))
    (X Y : Finset ℤ) : (#(X - Y) : ℝ) ≤ (#(X + Y) : ℝ) ^ lam := by
  rcases X.eq_empty_or_nonempty with rfl | hX
  · simp only [Finset.empty_sub, Finset.card_empty, Nat.cast_zero]; positivity
  rcases Y.eq_empty_or_nonempty with rfl | hY
  · simp only [Finset.sub_empty, Finset.card_empty, Nat.cast_zero]; positivity
  have hd : (0 : ℝ) < #(X - Y) := by exact_mod_cast (hX.sub hY).card_pos
  have hs : (0 : ℝ) < #(X + Y) := by exact_mod_cast (hX.add hY).card_pos
  rw [Real.le_rpow_iff_log_le hd hs]
  obtain ⟨Γ, hΓXY, hcard, hinj⟩ := exists_coupling X Y
  have hΓ : Γ.Nonempty := by
    rw [← Finset.card_pos, hcard, Finset.card_pos]
    exact hX.sub hY
  have key := hcert Γ X Y hΓ hinj hΓXY
  rw [hcard] at key
  linarith

/-- The constant of Tao's page 3a / GGSTW Problem 6.44: arbitrarily large `A, B ⊆ ℤ` with `|A + B| ≤ K|A|` and
`|A − B| ≥ c |A + B|^θ` for some fixed `K` and `c > 0`. -/
def AdmissibleK (θ : ℝ) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∃ c : ℝ, 0 < c ∧ ∀ n₀ : ℕ, ∃ A B : Finset ℤ,
    n₀ ≤ #A ∧ B.Nonempty ∧ (#(A + B) : ℝ) ≤ K * #A ∧ c * (#(A + B) : ℝ) ^ θ ≤ (#(A - B) : ℝ)

/-- `C_3a`, with the implied constants fixed along the sequence (`sSup ∅ = 0`). -/
noncomputable def thetaK : ℝ := sSup {t : ℝ | AdmissibleK t}

/-- An inequality `|A − B| ≤ C |A + B|^r` on the window `|A + B| ≤ K|A|` bounds every exponent admissible
with this `K`. -/
theorem admissibleK_le_of_rpow_bound {θ r : ℝ}
    (hbound : ∀ K : ℝ, 0 < K → ∃ C : ℝ, 0 < C ∧ ∀ A B : Finset ℤ, A.Nonempty → B.Nonempty →
      (#(A + B) : ℝ) ≤ K * #A → (#(A - B) : ℝ) ≤ C * (#(A + B) : ℝ) ^ r)
    (h : AdmissibleK θ) : θ ≤ r := by
  obtain ⟨K, hK, c, hc, hAB⟩ := h
  obtain ⟨C, hC, hbd⟩ := hbound K hK
  by_contra hlt
  push Not at hlt
  set δ : ℝ := θ - r with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  set M : ℝ := C / c with hMdef
  have hMpos : 0 < M := by rw [hMdef]; positivity
  set N : ℕ := ⌈M ^ (1 / δ)⌉₊ + 1 with hNdef
  obtain ⟨A, B, hcard, hBne, hsmall, hlow⟩ := hAB (max N 1)
  have hAne : A.Nonempty := by
    rw [← card_pos]
    have : 1 ≤ #A := le_trans (le_max_right N 1) hcard
    omega
  have hs : (0 : ℝ) < #(A + B) := by exact_mod_cast (hAne.add hBne).card_pos
  have hsN : (N : ℝ) ≤ (#(A + B) : ℝ) := by
    have h1 : #A ≤ #(A + B) := card_le_card_add_right hBne
    have h2 : N ≤ #A := le_trans (le_max_left N 1) hcard
    exact_mod_cast le_trans h2 h1
  have hbig : M ^ (1 / δ) < (#(A + B) : ℝ) := by
    have h1 := Nat.le_ceil (M ^ (1 / δ))
    have hN : (N : ℝ) = (⌈M ^ (1 / δ)⌉₊ : ℝ) + 1 := by rw [hNdef]; push_cast; ring
    rw [hN] at hsN
    linarith
  have hupper := hbd A B hAne hBne hsmall
  have hsplit : (#(A + B) : ℝ) ^ θ = (#(A + B) : ℝ) ^ δ * (#(A + B) : ℝ) ^ r := by
    rw [← Real.rpow_add hs, hδdef]; ring_nf
  have hrpos : (0 : ℝ) < (#(A + B) : ℝ) ^ r := Real.rpow_pos_of_pos hs r
  have hcontr : c * (#(A + B) : ℝ) ^ δ ≤ C := by
    have hchain : c * (#(A + B) : ℝ) ^ θ ≤ C * (#(A + B) : ℝ) ^ r := le_trans hlow hupper
    rw [hsplit] at hchain
    have : (c * (#(A + B) : ℝ) ^ δ) * (#(A + B) : ℝ) ^ r ≤ C * (#(A + B) : ℝ) ^ r := by
      nlinarith
    exact le_of_mul_le_mul_right this hrpos
  have hgt : M < (#(A + B) : ℝ) ^ δ := by
    have h2 : (M ^ (1 / δ)) ^ δ < ((#(A + B) : ℝ)) ^ δ :=
      Real.rpow_lt_rpow (by positivity) hbig hδ
    rwa [← Real.rpow_mul hMpos.le, one_div, inv_mul_cancel₀ (ne_of_gt hδ), Real.rpow_one] at h2
  rw [hMdef, div_lt_iff₀ hc] at hgt
  nlinarith

/-- For every `J ≥ 1`, a pair ceiling gives `θ ≤ 2 − 1/λ + 1/J` for exponents admissible with fixed `K`. -/
theorem admissibleK_le_J {θ lam : ℝ} (hlam : 1 ≤ lam)
    (hpair : ∀ X Y : Finset ℤ, (#(X - Y) : ℝ) ≤ (#(X + Y) : ℝ) ^ lam)
    (h : AdmissibleK θ) {J : ℕ} (hJ : 1 ≤ J) : θ ≤ 2 - 1 / lam + 1 / J := by
  have hlam0 : 0 < lam := by linarith
  have ha : 0 ≤ 1 - 1 / lam := by rw [sub_nonneg, div_le_one hlam0]; exact hlam
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast hJ
  set e : ℝ := 1 + J * (1 - 1 / lam) with he
  have he0 : 0 ≤ e := by positivity
  refine admissibleK_le_of_rpow_bound (fun K hK => ?_) h
  obtain ⟨k, hk⟩ : ∃ k : ℝ, k = K ^ (2 * 4 ^ J) := ⟨_, rfl⟩
  have hk0 : 0 < k := by rw [hk]; positivity
  refine ⟨k ^ (e / J), by positivity, fun A B hA hB hs => ?_⟩
  have hmain := MultiScale.card_sub_pow_le_multiscale (C := 1) hA hB hs hlam one_pos
    (fun X _ => by simpa using hpair X B) J
  rw [← hk, Real.one_rpow, one_mul] at hmain
  have hm0 : (0 : ℝ) < #A := by exact_mod_cast hA.card_pos
  have hms : (#A : ℝ) ≤ #(A + B) := by exact_mod_cast card_le_card_add_right hB
  have hs0 : (0 : ℝ) < #(A + B) := hm0.trans_le hms
  set s : ℝ := (#(A + B) : ℝ)
  set d : ℝ := (#(A - B) : ℝ)
  have hd0 : 0 ≤ d := by positivity
  have hks : 0 ≤ k * s := by positivity
  have hkse : 0 ≤ (k * s) ^ e := Real.rpow_nonneg hks _
  have hJi : (0 : ℝ) ≤ 1 / (J : ℝ) := by positivity
  have h2 : (k * #A) ^ e ≤ (k * s) ^ e :=
    Real.rpow_le_rpow (by positivity) (by gcongr) he0
  have hdJ : d ^ J ≤ s ^ J * (k * s) ^ e := hmain.trans (by gcongr)
  have hJne : (J : ℝ) ≠ 0 := hJ0.ne'
  have hroot : d = (d ^ J) ^ (1 / (J : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hd0, mul_one_div_cancel hJne, Real.rpow_one]
  rw [hroot]
  calc (d ^ J) ^ (1 / (J : ℝ)) ≤ (s ^ J * (k * s) ^ e) ^ (1 / (J : ℝ)) :=
        Real.rpow_le_rpow (pow_nonneg hd0 _) hdJ hJi
    _ = s * (k * s) ^ (e / J) := by
        rw [Real.mul_rpow (pow_nonneg hs0.le _) hkse, ← Real.rpow_natCast,
          ← Real.rpow_mul hs0.le, mul_one_div_cancel hJne, Real.rpow_one,
          ← Real.rpow_mul hks, mul_one_div]
    _ = k ^ (e / J) * s ^ (2 - 1 / lam + 1 / J) := by
        rw [Real.mul_rpow hk0.le hs0.le]
        have : (2 : ℝ) - 1 / lam + 1 / J = 1 + e / J := by
          rw [he]; field_simp; ring
        rw [this, Real.rpow_add hs0, Real.rpow_one]; ring

/-- Every exponent admissible with fixed constants is at most `2 − 1/λ`. -/
theorem admissibleK_le {θ lam : ℝ} (hlam : 1 ≤ lam)
    (hpair : ∀ X Y : Finset ℤ, (#(X - Y) : ℝ) ≤ (#(X + Y) : ℝ) ^ lam)
    (h : AdmissibleK θ) : θ ≤ 2 - 1 / lam := by
  by_contra hlt
  push Not at hlt
  obtain ⟨J, hJ⟩ := exists_nat_gt (1 / (θ - (2 - 1 / lam)))
  have hpos : 0 < θ - (2 - 1 / lam) := by linarith
  have hJ1 : 1 ≤ J := by
    have : (0 : ℝ) < J := lt_trans (by positivity) hJ
    exact_mod_cast this
  have hb := admissibleK_le_J hlam hpair h hJ1
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast hJ1
  have : 1 / (J : ℝ) < θ - (2 - 1 / lam) := by
    rw [div_lt_iff₀ hJ0]
    rw [div_lt_iff₀ hpos] at hJ
    linarith
  linarith

/-- **Transfer for the fixed-constant reading**: `thetaK ≤ 2 − 1/λ`. -/
theorem thetaK_le_of_pair_ceiling {lam : ℝ}
    (hpair : ∀ X Y : Finset ℤ, (#(X - Y) : ℝ) ≤ (#(X + Y) : ℝ) ^ lam) : thetaK ≤ 2 - 1 / lam := by
  have hlam := one_le_of_pair_ceiling hpair
  refine Real.sSup_le (fun _ ht => admissibleK_le hlam hpair ht) ?_
  rw [sub_nonneg, div_le_iff₀ (by linarith)]
  linarith

/-- `theta` (Kleinwaks: every `K`) is at most `thetaK` (some `K`). -/
theorem theta_le_thetaK_of_admissible {θ : ℝ} (h : Admissible θ) : AdmissibleK θ := by
  obtain ⟨-, hfam⟩ := h
  obtain ⟨c, hc, hAB⟩ := hfam 2 one_lt_two
  exact ⟨2, two_pos, c, hc, hAB⟩

end EntropyBounds.TwoSet
