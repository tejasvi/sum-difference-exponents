import EntropyBounds.Glue.SetForm

/-!
# Without injectivity: the random-selection reduction

`entropy_of_injective`: if `H(X, Y) ≤ a H(X) + b H(Y) + c H(X + Y)` (`a, b, c ≥ 0`) holds for every finitely supported
real pair whose difference is injective on the support, then

  `H(X − Y) ≤ a H(X) + b H(Y) + c H(X + Y)`

for every finitely supported real pair (no injectivity assumption).

Proof (the reduction of Tao, arXiv:2511.15135, proof of Prop. 3.6, in a finite form).  For every value `z` of
`Z = X − Y`, let `φ z` be a random point of the fiber `F z = {q : q.1 − q.2 = z}` with the conditional law of `(X, Y)`
given `Z = z`, independently over `z`: a product law `w` on the finite set of selectors `φ`.  For a fixed selector,
the pair `φ(Z)` has injective difference and the entropy of `Z`, so the hypothesis gives
`H(Z) ≤ a H_φ(X') + b H_φ(Y') + c H_φ(X' + Y')`.  Averaged over `φ`, the laws of `X'`, `Y'` and `X' + Y'` are those of
`X`, `Y` and `X + Y` (the marginals of `w` are the conditional laws), and entropy is concave (Jensen's inequality
for `negMulLog`), so the averages of the right-hand sides are at most `a H(X) + b H(Y) + c H(X + Y)`.
-/

open Finset

namespace EntropyBounds.Glue

open SumsDifferences

/-- The entropy of a law, summed over any finite superset of its values. -/
theorem pushEntropy_eq_sum_superset {ι α : Type*} [DecidableEq α] {s : Finset ι} {p : ι → ℝ} {f : ι → α}
    {T : Finset α} (hT : s.image f ⊆ T) :
    pushEntropy s p f = ∑ a ∈ T, Real.negMulLog (pushWeight s p f a) := by
  unfold pushEntropy entropy
  refine Finset.sum_subset hT fun a _ ha => ?_
  have h0 : pushWeight s p f a = 0 := by
    unfold pushWeight
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi' := Finset.mem_filter.mp hi
    exact absurd (Finset.mem_image.mpr ⟨i, hi'.1, hi'.2⟩) ha
  rw [h0, Real.negMulLog_zero]

/-- **Concavity of entropy** for a finite mixture of laws (Jensen for `negMulLog`). -/
theorem sum_negMulLog_mix {κ α : Type*} {Φ : Finset κ} {w : κ → ℝ} (hw : ∀ φ ∈ Φ, 0 ≤ w φ)
    (hw1 : ∑ φ ∈ Φ, w φ = 1) (T : Finset α) (μ : κ → α → ℝ) (hμ : ∀ φ ∈ Φ, ∀ a ∈ T, 0 ≤ μ φ a) :
    ∑ φ ∈ Φ, w φ * ∑ a ∈ T, Real.negMulLog (μ φ a) ≤ ∑ a ∈ T, Real.negMulLog (∑ φ ∈ Φ, w φ * μ φ a) := by
  have e : ∑ φ ∈ Φ, w φ * ∑ a ∈ T, Real.negMulLog (μ φ a)
      = ∑ a ∈ T, ∑ φ ∈ Φ, w φ * Real.negMulLog (μ φ a) := by
    simp_rw [Finset.mul_sum]
    exact Finset.sum_comm
  rw [e]
  refine Finset.sum_le_sum fun a ha => ?_
  have h := Real.concaveOn_negMulLog.le_map_sum (t := Φ) (w := w) (p := fun φ => μ φ a) hw hw1
    (fun φ hφ => Set.mem_Ici.mpr (hμ φ hφ a ha))
  simpa only [smul_eq_mul] using h

/-- **The random-selection reduction.** -/
theorem entropy_of_injective {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hent : ∀ (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ), (∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') →
      (∀ q ∈ Γ, 0 ≤ p q) → ∑ q ∈ Γ, p q = 1 →
      pushEntropy Γ p (fun q => q) ≤ a * pushEntropy Γ p (fun q => q.1) + b * pushEntropy Γ p (fun q => q.2)
        + c * pushEntropy Γ p (fun q => q.1 + q.2))
    (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (hp : ∀ q ∈ Γ, 0 ≤ p q) (hs : ∑ q ∈ Γ, p q = 1) :
    pushEntropy Γ p (fun q => q.1 - q.2) ≤ a * pushEntropy Γ p (fun q => q.1)
      + b * pushEntropy Γ p (fun q => q.2) + c * pushEntropy Γ p (fun q => q.1 + q.2) := by
  classical
  -- the difference and its fibers
  let d : ℝ × ℝ → ℝ := fun q => q.1 - q.2
  let D : Finset ℝ := Γ.image d
  let F : D → Finset (ℝ × ℝ) := fun z => Γ.filter (fun q => d q = z.1)
  let P : D → ℝ := fun z => ∑ q ∈ F z, p q
  have hPw : ∀ z : D, P z = pushWeight Γ p d z.1 := fun z => rfl
  have hFsub : ∀ z : D, F z ⊆ Γ := fun z => Finset.filter_subset _ _
  have hFd : ∀ z : D, ∀ q ∈ F z, d q = z.1 := fun z q hq => (Finset.mem_filter.mp hq).2
  have hFne : ∀ z : D, (F z).Nonempty := by
    intro z
    obtain ⟨q, hq, hqz⟩ := Finset.mem_image.mp z.2
    exact ⟨q, Finset.mem_filter.mpr ⟨hq, hqz⟩⟩
  have hP0 : ∀ z : D, 0 ≤ P z := fun z => Finset.sum_nonneg fun q hq => hp q (hFsub z hq)
  -- conditional laws on the fibers (uniform on fibers of mass zero)
  let pz : D → ℝ × ℝ → ℝ := fun z q => if P z = 0 then ((#(F z) : ℝ))⁻¹ else p q / P z
  have hpz0 : ∀ z : D, ∀ q ∈ F z, 0 ≤ pz z q := by
    intro z q hq
    simp only [pz]
    split_ifs
    · positivity
    · exact div_nonneg (hp q (hFsub z hq)) (hP0 z)
  have hpz1 : ∀ z : D, ∑ q ∈ F z, pz z q = 1 := by
    intro z
    simp only [pz]
    by_cases h : P z = 0
    · simp only [h, if_true, Finset.sum_const, nsmul_eq_mul]
      have : (0 : ℝ) < #(F z) := by exact_mod_cast (hFne z).card_pos
      field_simp
    · simp only [h, if_false]
      rw [← Finset.sum_div]
      exact div_self h
  have hPpz : ∀ z : D, ∀ q ∈ F z, P z * pz z q = p q := by
    intro z q hq
    simp only [pz]
    by_cases h : P z = 0
    · have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun q' hq' => hp q' (hFsub z hq'))).mp h q hq
      rw [h, zero_mul, hzero]
    · rw [if_neg h]
      field_simp
  -- the selectors and their product law
  let Φ : Finset (D → ℝ × ℝ) := Fintype.piFinset F
  let w : (D → ℝ × ℝ) → ℝ := fun φ => ∏ z, pz z (φ z)
  have hw0 : ∀ φ ∈ Φ, 0 ≤ w φ := by
    intro φ hφ
    exact Finset.prod_nonneg fun z _ => hpz0 z (φ z) (Fintype.mem_piFinset.mp hφ z)
  have hmarg : ∀ (z₀ : D) (g : ℝ × ℝ → ℝ), ∑ φ ∈ Φ, w φ * g (φ z₀) = ∑ q ∈ F z₀, pz z₀ q * g q := by
    intro z₀ g
    let h : ∀ z : D, ℝ × ℝ → ℝ := fun z q => pz z q * (if z = z₀ then g q else 1)
    have e1 : ∀ φ : D → ℝ × ℝ, w φ * g (φ z₀) = ∏ z, h z (φ z) := by
      intro φ
      simp only [h, w]
      rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ z₀ (fun z => g (φ z)),
        if_pos (Finset.mem_univ z₀)]
    rw [Finset.sum_congr rfl fun φ _ => e1 φ, ← Finset.prod_univ_sum]
    rw [Fintype.prod_eq_single z₀]
    · simp only [h, ↓reduceIte]
    · intro z hz
      simp only [h, if_neg hz, mul_one]
      exact hpz1 z
  have hw1 : ∑ φ ∈ Φ, w φ = 1 := by
    have e : ∑ φ ∈ Φ, w φ = ∏ z, ∑ q ∈ F z, pz z q := by
      rw [Finset.prod_univ_sum]
    rw [e]
    exact Finset.prod_eq_one fun z _ => hpz1 z
  -- for a fixed selector: an injective pair with the law of `Z`
  let Γφ : (D → ℝ × ℝ) → Finset (ℝ × ℝ) := fun φ => Finset.univ.image φ
  let pφ : ℝ × ℝ → ℝ := fun q => pushWeight Γ p d (d q)
  have hφd : ∀ φ ∈ Φ, ∀ z : D, d (φ z) = z.1 := fun φ hφ z => hFd z (φ z) (Fintype.mem_piFinset.mp hφ z)
  have hφinj : ∀ φ ∈ Φ, Function.Injective φ := by
    intro φ hφ z z' h
    apply Subtype.ext
    rw [← hφd φ hφ z, ← hφd φ hφ z', h]
  have hpφ : ∀ φ ∈ Φ, ∀ z : D, pφ (φ z) = P z := by
    intro φ hφ z
    simp only [pφ]
    rw [hφd φ hφ z, hPw z]
  have hsub : ∀ φ ∈ Φ, Γφ φ ⊆ Γ := by
    intro φ hφ q hq
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hq
    exact hFsub z (Fintype.mem_piFinset.mp hφ z)
  have hsumD : ∑ z : D, P z = 1 := by
    rw [show ∑ z : D, P z = ∑ t ∈ D, pushWeight Γ p d t from Finset.sum_coe_sort D (fun t => pushWeight Γ p d t),
      sum_pushWeight, hs]
  have hkey : ∀ φ ∈ Φ, pushEntropy (Γφ φ) pφ (fun q => q) ≤ a * pushEntropy (Γφ φ) pφ (fun q => q.1)
      + b * pushEntropy (Γφ φ) pφ (fun q => q.2) + c * pushEntropy (Γφ φ) pφ (fun q => q.1 + q.2) := by
    intro φ hφ
    refine hent (Γφ φ) pφ ?_ (fun q _ => pushWeight_nonneg hp _) ?_
    · intro q hq q' hq' hqq
      obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨z', _, rfl⟩ := Finset.mem_image.mp hq'
      have : z = z' := by
        apply Subtype.ext
        rw [← hφd φ hφ z, ← hφd φ hφ z']
        exact hqq
      rw [this]
    · simp only [Γφ]
      rw [Finset.sum_image fun z _ z' _ h => hφinj φ hφ h]
      rw [Finset.sum_congr rfl fun z _ => hpφ φ hφ z]
      exact hsumD
  -- `H(φ(Z)) = H(Z)`
  have hid : ∀ φ ∈ Φ, pushEntropy (Γφ φ) pφ (fun q => q) = pushEntropy Γ p d := by
    intro φ hφ
    rw [pushEntropy_id_eq_entropy]
    unfold entropy
    simp only [Γφ]
    rw [Finset.sum_image fun z _ z' _ h => hφinj φ hφ h]
    rw [Finset.sum_congr rfl fun z _ => by rw [hpφ φ hφ z]]
    rw [show ∑ z : D, Real.negMulLog (P z) = ∑ t ∈ D, Real.negMulLog (pushWeight Γ p d t) from
      Finset.sum_coe_sort D (fun t => Real.negMulLog (pushWeight Γ p d t))]
    rfl
  -- the averaged laws are the laws of `X`, `Y`, `X + Y`
  have hpw : ∀ φ ∈ Φ, ∀ (g : ℝ × ℝ → ℝ) (t : ℝ),
      pushWeight (Γφ φ) pφ g t = ∑ z : D, if g (φ z) = t then P z else 0 := by
    intro φ hφ g t
    unfold pushWeight
    rw [Finset.sum_filter]
    simp only [Γφ]
    rw [Finset.sum_image fun z _ z' _ h => hφinj φ hφ h]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [hpφ φ hφ z]
  have hmix : ∀ (g : ℝ × ℝ → ℝ) (t : ℝ), ∑ φ ∈ Φ, w φ * pushWeight (Γφ φ) pφ g t = pushWeight Γ p g t := by
    intro g t
    rw [Finset.sum_congr rfl fun φ hφ => by rw [hpw φ hφ g t]]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl fun z _ => hmarg z (fun q => if g q = t then P z else 0)]
    have e2 : ∀ z : D, ∑ q ∈ F z, pz z q * (if g q = t then P z else 0)
        = ∑ q ∈ F z, (if g q = t then p q else 0) := by
      intro z
      refine Finset.sum_congr rfl fun q hq => ?_
      split_ifs
      · rw [mul_comm]; exact hPpz z q hq
      · rw [mul_zero]
    rw [Finset.sum_congr rfl fun z _ => e2 z]
    rw [show ∑ z : D, ∑ q ∈ F z, (if g q = t then p q else 0)
        = ∑ s ∈ D, ∑ q ∈ Γ.filter (fun q => d q = s), (if g q = t then p q else 0) from
      Finset.sum_coe_sort D (fun s => ∑ q ∈ Γ.filter (fun q => d q = s), (if g q = t then p q else 0))]
    rw [Finset.sum_fiberwise_of_maps_to (fun q hq => Finset.mem_image_of_mem d hq)]
    unfold pushWeight
    rw [Finset.sum_filter]
  -- concavity
  have hconc : ∀ g : ℝ × ℝ → ℝ, ∑ φ ∈ Φ, w φ * pushEntropy (Γφ φ) pφ g ≤ pushEntropy Γ p g := by
    intro g
    have hT : ∀ φ ∈ Φ, (Γφ φ).image g ⊆ Γ.image g := fun φ hφ => Finset.image_subset_image (hsub φ hφ)
    rw [Finset.sum_congr rfl fun φ hφ => by rw [pushEntropy_eq_sum_superset (hT φ hφ)]]
    refine (sum_negMulLog_mix hw0 hw1 (Γ.image g) (fun φ t => pushWeight (Γφ φ) pφ g t)
      (fun φ _ t _ => pushWeight_nonneg (fun q _ => pushWeight_nonneg hp _) t)).trans ?_
    rw [pushEntropy_eq_sum_superset (Finset.Subset.refl (Γ.image g))]
    exact le_of_eq (Finset.sum_congr rfl fun t _ => by rw [hmix g t])
  -- combine
  have h1 : pushEntropy Γ p d = ∑ φ ∈ Φ, w φ * pushEntropy (Γφ φ) pφ (fun q => q) := by
    rw [Finset.sum_congr rfl fun φ hφ => by rw [hid φ hφ], ← Finset.sum_mul, hw1, one_mul]
  have h2 : ∑ φ ∈ Φ, w φ * pushEntropy (Γφ φ) pφ (fun q => q)
      ≤ ∑ φ ∈ Φ, w φ * (a * pushEntropy (Γφ φ) pφ (fun q => q.1)
        + b * pushEntropy (Γφ φ) pφ (fun q => q.2) + c * pushEntropy (Γφ φ) pφ (fun q => q.1 + q.2)) :=
    Finset.sum_le_sum fun φ hφ => mul_le_mul_of_nonneg_left (hkey φ hφ) (hw0 φ hφ)
  have h3 : ∑ φ ∈ Φ, w φ * (a * pushEntropy (Γφ φ) pφ (fun q => q.1)
        + b * pushEntropy (Γφ φ) pφ (fun q => q.2) + c * pushEntropy (Γφ φ) pφ (fun q => q.1 + q.2))
      = a * ∑ φ ∈ Φ, w φ * pushEntropy (Γφ φ) pφ (fun q => q.1)
        + b * ∑ φ ∈ Φ, w φ * pushEntropy (Γφ φ) pφ (fun q => q.2)
        + c * ∑ φ ∈ Φ, w φ * pushEntropy (Γφ φ) pφ (fun q => q.1 + q.2) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun φ _ => by ring
  have hX := mul_le_mul_of_nonneg_left (hconc (fun q => q.1)) ha
  have hY := mul_le_mul_of_nonneg_left (hconc (fun q => q.2)) hb
  have hS := mul_le_mul_of_nonneg_left (hconc (fun q => q.1 + q.2)) hc
  show pushEntropy Γ p d ≤ _
  rw [h1]
  linarith [h2, h3, hX, hY, hS]

/-- The `max` form: `H(X − Y) ≤ (a + b + c) max(H(X), H(Y), H(X + Y))`. -/
theorem entropy_max_of_injective {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hent : ∀ (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ), (∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') →
      (∀ q ∈ Γ, 0 ≤ p q) → ∑ q ∈ Γ, p q = 1 →
      pushEntropy Γ p (fun q => q) ≤ a * pushEntropy Γ p (fun q => q.1) + b * pushEntropy Γ p (fun q => q.2)
        + c * pushEntropy Γ p (fun q => q.1 + q.2))
    (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (hp : ∀ q ∈ Γ, 0 ≤ p q) (hs : ∑ q ∈ Γ, p q = 1) :
    pushEntropy Γ p (fun q => q.1 - q.2) ≤ (a + b + c) *
      max (max (pushEntropy Γ p (fun q => q.1)) (pushEntropy Γ p (fun q => q.2)))
        (pushEntropy Γ p (fun q => q.1 + q.2)) := by
  have h := entropy_of_injective ha hb hc hent Γ p hp hs
  set M := max (max (pushEntropy Γ p (fun q => q.1)) (pushEntropy Γ p (fun q => q.2)))
    (pushEntropy Γ p (fun q => q.1 + q.2))
  have hX : pushEntropy Γ p (fun q => q.1) ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
  have hY : pushEntropy Γ p (fun q => q.2) ≤ M := le_trans (le_max_right _ _) (le_max_left _ _)
  have hS : pushEntropy Γ p (fun q => q.1 + q.2) ≤ M := le_max_right _ _
  nlinarith [mul_le_mul_of_nonneg_left hX ha, mul_le_mul_of_nonneg_left hY hb, mul_le_mul_of_nonneg_left hS hc]

end EntropyBounds.Glue
