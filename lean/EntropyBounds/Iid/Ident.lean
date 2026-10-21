import EntropyBounds.Iid.Indep

/-!
# Grid identifications: the law of a sum of coordinates of distinct copies

A *grid form* uses each copy at most once, through `x_k` or `y_k` with coefficient `1`.  The coordinates it uses
are independent, with laws `μ = margFst Γ` (for `x`) and `ν = margSnd Γ` (for `y`), so its law is the convolution
`μ^i ν^j = P μ ν i j` (`i`, `j` the numbers of `x`- and `y`-coordinates used) and

  `HLm Γ m [f] = h(i, j) = ent (P μ ν i j)`      (`HLm_grid`, Boolean form `HLm_gridB`).

The law is computed by induction on the number of copies (`law_grid`), splitting off copy `0`.
-/

open Finset

namespace EntropyBounds.Iid

open SumsDifferences SumsDifferences.CoupledEntropy SumsDifferences.CoupledForms

variable {m : ℕ}

/-- Every coefficient is `(0,0)`, `(1,0)` or `(0,1)` (Boolean, checked by `decide`). -/
def gridB (f : Form m) : Bool :=
  (List.finRange m).all fun k => f k == (0, 0) || f k == (1, 0) || f k == (0, 1)

/-- Number of `x`-coordinates used. -/
def cntXL (f : Form m) : ℕ := ((List.finRange m).filter fun k => f k == (1, 0)).length

/-- Number of `y`-coordinates used. -/
def cntYL (f : Form m) : ℕ := ((List.finRange m).filter fun k => f k == (0, 1)).length

/-! ## One coordinate term -/

theorem law_zero {Γ : Finset (ℤ × ℤ)} (hΓ : Γ.Nonempty) (F : ℤ × ℤ → ℤ) (hF : ∀ p, F p = 0) (z : ℤ) :
    pushWeight Γ (fun _ => (#Γ : ℝ)⁻¹) F z = (P (margFst Γ) (margSnd Γ) 0 0) z := by
  classical
  rw [show P (margFst Γ) (margSnd Γ) 0 0 = 1 by simp [P], AddMonoidAlgebra.one_def,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  simp only [pushWeight, hF]
  by_cases hz : (0 : ℤ) = z
  · rw [ite_eq_left hz, Finset.filter_true_of_mem (fun _ _ => hz), uniform_sum hΓ]
  · rw [ite_eq_right hz, Finset.filter_false_of_mem (fun _ _ => hz), Finset.sum_empty]

theorem law_x {Γ : Finset (ℤ × ℤ)} (F : ℤ × ℤ → ℤ) (hF : ∀ p, F p = p.1) (z : ℤ) :
    pushWeight Γ (fun _ => (#Γ : ℝ)⁻¹) F z = (P (margFst Γ) (margSnd Γ) 1 0) z := by
  simp only [P, pow_one, pow_zero, mul_one]
  rw [← pushWeight_fst_eq_margFst Γ z]
  simp only [pushWeight, hF]

theorem law_y {Γ : Finset (ℤ × ℤ)} (F : ℤ × ℤ → ℤ) (hF : ∀ p, F p = p.2) (z : ℤ) :
    pushWeight Γ (fun _ => (#Γ : ℝ)⁻¹) F z = (P (margFst Γ) (margSnd Γ) 0 1) z := by
  simp only [P, pow_one, pow_zero, one_mul]
  rw [← pushWeight_snd_eq_margSnd Γ z]
  simp only [pushWeight, hF]

/-! ## Splitting off copy `0` -/

/-- `Γ^(m+1) ≅ Γ × Γ^m`. -/
def splitHead : (Fin (m + 1) → ℤ × ℤ) → (ℤ × ℤ) × (Fin m → ℤ × ℤ) := fun q => (q 0, Fin.tail q)

theorem splitHead_injOn (Γ : Finset (ℤ × ℤ)) :
    Set.InjOn (splitHead (m := m)) (Om Γ (m + 1) : Set _) := by
  intro q _ q' _ h
  simp only [splitHead, Prod.mk.injEq] at h
  rw [← Fin.cons_self_tail q, ← Fin.cons_self_tail q', h.1, h.2]

theorem image_splitHead (Γ : Finset (ℤ × ℤ)) :
    (Om Γ (m + 1)).image splitHead = Γ ×ˢ Om Γ m := by
  ext ⟨p, r⟩
  simp only [Finset.mem_image, Finset.mem_product, Om, Fintype.mem_piFinset, splitHead, Prod.mk.injEq]
  constructor
  · rintro ⟨q, hq, rfl, rfl⟩; exact ⟨hq 0, fun k => hq k.succ⟩
  · rintro ⟨hp, hr⟩
    refine ⟨Fin.cons p r, fun k => ?_, by simp, by simp⟩
    refine Fin.cases ?_ (fun k => ?_) k
    · simpa using hp
    · simpa using hr k

theorem fval_succ (f : Form (m + 1)) (q : Fin (m + 1) → ℤ × ℤ) :
    fval f q = ((f 0).1 * (q 0).1 + (f 0).2 * (q 0).2) + fval (Fin.tail f) (Fin.tail q) := by
  simp only [fval, Fin.sum_univ_succ, Fin.tail]

theorem cntXL_succ (f : Form (m + 1)) :
    cntXL f = (if f 0 = (1, 0) then 1 else 0) + cntXL (Fin.tail f) := by
  simp only [cntXL, List.finRange_succ, List.filter_cons, List.filter_map, List.length_map, Fin.tail,
    Function.comp_def]
  split_ifs with h1 h2 h2 <;> simp_all <;> omega

theorem cntYL_succ (f : Form (m + 1)) :
    cntYL f = (if f 0 = (0, 1) then 1 else 0) + cntYL (Fin.tail f) := by
  simp only [cntYL, List.finRange_succ, List.filter_cons, List.filter_map, List.length_map, Fin.tail,
    Function.comp_def]
  split_ifs with h1 h2 h2 <;> simp_all <;> omega

theorem gridB_succ {f : Form (m + 1)} (h : gridB f = true) :
    (f 0 = (0, 0) ∨ f 0 = (1, 0) ∨ f 0 = (0, 1)) ∧ gridB (Fin.tail f) = true := by
  simp only [gridB, List.finRange_succ, List.all_cons, List.all_map, Bool.and_eq_true,
    Bool.or_eq_true, beq_iff_eq, Function.comp_def] at h ⊢
  refine ⟨by tauto, ?_⟩
  simpa [Fin.tail] using h.2

/-- **The law of a grid form.** -/
theorem law_grid {Γ : Finset (ℤ × ℤ)} (hΓ : Γ.Nonempty) :
    ∀ (m : ℕ) (f : Form m), gridB f = true → ∀ z,
      pushWeight (Om Γ m) (wt Γ m) (fval f) z = (P (margFst Γ) (margSnd Γ) (cntXL f) (cntYL f)) z := by
  classical
  intro m
  induction m with
  | zero =>
    intro f _ z
    have hX : cntXL f = 0 := by simp [cntXL]
    have hY : cntYL f = 0 := by simp [cntYL]
    rw [hX, hY]
    have hO : Om Γ 0 = {Fin.elim0} := by
      ext q; simp only [Om, Fintype.mem_piFinset, IsEmpty.forall_iff, Finset.mem_singleton, true_iff]
      funext k; exact k.elim0
    have h0 : ∀ q : Fin 0 → ℤ × ℤ, fval f q = 0 := fun q => by simp [fval]
    rw [show P (margFst Γ) (margSnd Γ) 0 0 = 1 by simp [P], AddMonoidAlgebra.one_def,
      AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    simp only [pushWeight, h0, hO, wt]
    by_cases hz : (0 : ℤ) = z
    · rw [ite_eq_left hz, Finset.filter_true_of_mem (fun _ _ => hz), Finset.sum_singleton, pow_zero]
    · rw [ite_eq_right hz, Finset.filter_false_of_mem (fun _ _ => hz), Finset.sum_empty]
  | succ m ih =>
    intro f hf z
    obtain ⟨h0, htl⟩ := gridB_succ hf
    have hIH := ih (Fin.tail f) htl
    have hre := pushWeight_reindex (Ω := Om Γ (m + 1)) (p := wt Γ (m + 1))
      (p' := productLaw (fun _ : ℤ × ℤ => (#Γ : ℝ)⁻¹) (wt Γ m)) splitHead (splitHead_injOn Γ)
      (fun q _ => by simp only [productLaw, wt, pow_succ]; ring)
      (fun w : (ℤ × ℤ) × (Fin m → ℤ × ℤ) => ((f 0).1 * w.1.1 + (f 0).2 * w.1.2) + fval (Fin.tail f) w.2) z
    have e1 : (fval f : (Fin (m + 1) → ℤ × ℤ) → ℤ) = fun q =>
        (fun w : (ℤ × ℤ) × (Fin m → ℤ × ℤ) => ((f 0).1 * w.1.1 + (f 0).2 * w.1.2) + fval (Fin.tail f) w.2)
          (splitHead q) := by
      funext q; simp only [splitHead, fval_succ]
    rw [e1, hre, image_splitHead]
    rw [cntXL_succ, cntYL_succ]
    rcases h0 with h0 | h0 | h0
    · have hconv := pushWeight_add_eq_mul (G := ℤ) (Ω₁ := Γ) (Ω₂ := Om Γ m) (w₁ := fun _ => (#Γ : ℝ)⁻¹)
        (w₂ := wt Γ m) (F₁ := fun p : ℤ × ℤ => (f 0).1 * p.1 + (f 0).2 * p.2) (F₂ := fval (Fin.tail f))
        (law_zero hΓ _ (fun p => by rw [h0]; ring)) hIH z
      rw [hconv, P_mul, h0]
      simp
    · have hconv := pushWeight_add_eq_mul (G := ℤ) (Ω₁ := Γ) (Ω₂ := Om Γ m) (w₁ := fun _ => (#Γ : ℝ)⁻¹)
        (w₂ := wt Γ m) (F₁ := fun p : ℤ × ℤ => (f 0).1 * p.1 + (f 0).2 * p.2) (F₂ := fval (Fin.tail f))
        (law_x _ (fun p => by rw [h0]; ring)) hIH z
      rw [hconv, P_mul, h0]
      simp [add_comm]
    · have hconv := pushWeight_add_eq_mul (G := ℤ) (Ω₁ := Γ) (Ω₂ := Om Γ m) (w₁ := fun _ => (#Γ : ℝ)⁻¹)
        (w₂ := wt Γ m) (F₁ := fun p : ℤ × ℤ => (f 0).1 * p.1 + (f 0).2 * p.2) (F₂ := fval (Fin.tail f))
        (law_y _ (fun p => by rw [h0]; ring)) hIH z
      rw [hconv, P_mul, h0]
      simp [add_comm]

theorem HLm_single_eq {Γ : Finset (ℤ × ℤ)} (f : Form m) :
    HLm Γ m [f] = pushEntropy (Om Γ m) (wt Γ m) (fval f) := by
  refine pushEntropy_eq_of_comp (wt_nonneg Γ m) (fun y => y.headD 0) (fun z => [z]) ?_ ?_
  · intro q _; simp
  · intro q _; simp

/-- **Grid identification** (Boolean form): `H(f) = h(i, j)`. -/
theorem HLm_gridB {Γ : Finset (ℤ × ℤ)} (hΓ : Γ.Nonempty) (f : Form m) (i j : ℕ)
    (h : (gridB f && cntXL f == i && cntYL f == j) = true) :
    HLm Γ m [f] = ent (P (margFst Γ) (margSnd Γ) i j) := by
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hg, hi⟩, hj⟩ := h
  rw [HLm_single_eq]
  refine pushEntropy_eq_ent fun z => ?_
  rw [law_grid hΓ m f hg z, hi, hj]

end EntropyBounds.Iid
