import SumDifference.LinearFormsEntropy

/-!
# Joint entropies of integer linear forms in `m` independent copies of a coupled pair

Let `Γ ⊆ ℤ × ℤ` be a nonempty finite set of pairs with pairwise distinct differences and let `(X₁, Y₁)` be
uniform on `Γ`.  On the sample space `Om Γ m = Γ^m` (functions `q : Fin m → ℤ × ℤ` with every `q k ∈ Γ`) with the
uniform law, the pairs `q 0, …, q (m-1)` are `m` independent copies of `(X₁, Y₁)`.  A *form* `f : Form m` has
integer coefficients `(f k).1`, `(f k).2` on the coordinates `x_k = (q k).1`, `y_k = (q k).2`, and

  `HLm Γ m l = H((f(q))_{f ∈ l})`

is the joint entropy of a list of forms.  This generalises `HL` of `SumDifference.LinearFormsEntropy` (two copies)
to any number of copies.

* `HLm_eq_of_det`: two lists that determine each other have the same joint entropy.  `Det.gen` gives a
  determination from integer data that a Boolean check verifies: `c • f = Σ mᵢ lᵢ + g` with `c ≠ 0`, where the
  part `g` may only use `x_k, y_k` when `x_k − y_k` is an integer combination of `l` (distinct differences in `Γ`).
  Division by `c` is exact over `ℤ`.
* `HLm_submod`, `HLm_mono`, `HLm_nil`: Shannon facts.
-/

open Finset

namespace EntropyBounds.Iid

open SumsDifferences SumsDifferences.CoupledEntropy SumsDifferences.CoupledForms

/-- Coefficients of a form in the coordinates `(x_k, y_k)`, `k < m`. -/
abbrev Form (m : ℕ) := Fin m → ℤ × ℤ

variable {m : ℕ}

/-- The value of a form at a point of the sample space. -/
def fval (f : Form m) (q : Fin m → ℤ × ℤ) : ℤ := ∑ k, ((f k).1 * (q k).1 + (f k).2 * (q k).2)

/-- The sample space `Γ^m`. -/
def Om (Γ : Finset (ℤ × ℤ)) (m : ℕ) : Finset (Fin m → ℤ × ℤ) := Fintype.piFinset (fun _ => Γ)

/-- The uniform weight on `Γ^m`. -/
noncomputable def wt (Γ : Finset (ℤ × ℤ)) (m : ℕ) : (Fin m → ℤ × ℤ) → ℝ := fun _ => ((#Γ : ℝ)⁻¹) ^ m

theorem wt_nonneg (Γ : Finset (ℤ × ℤ)) (m : ℕ) : ∀ q ∈ Om Γ m, 0 ≤ wt Γ m q :=
  fun _ _ => by unfold wt; positivity

theorem card_Om (Γ : Finset (ℤ × ℤ)) (m : ℕ) : #(Om Γ m) = #Γ ^ m := by
  simp [Om, Fintype.card_piFinset]

theorem wt_sum {Γ : Finset (ℤ × ℤ)} (hΓ : Γ.Nonempty) (m : ℕ) : ∑ q ∈ Om Γ m, wt Γ m q = 1 := by
  have h : (0 : ℝ) < #Γ := by exact_mod_cast hΓ.card_pos
  simp only [wt, Finset.sum_const, card_Om, nsmul_eq_mul, Nat.cast_pow]
  rw [inv_pow, mul_inv_cancel₀ (by positivity)]

theorem mem_Om {Γ : Finset (ℤ × ℤ)} {q : Fin m → ℤ × ℤ} : q ∈ Om Γ m ↔ ∀ k, q k ∈ Γ := by
  simp [Om]

/-- Joint entropy of a list of forms. -/
noncomputable def HLm (Γ : Finset (ℤ × ℤ)) (m : ℕ) (l : List (Form m)) : ℝ :=
  pushEntropy (Om Γ m) (wt Γ m) (fun q => l.map fun f => fval f q)

/-! ## Computable vector arithmetic (cheap for the kernel) -/

/-- Sum of two forms. -/
def addF (f g : Form m) : Form m := fun k => ((f k).1 + (g k).1, (f k).2 + (g k).2)

/-- Integer multiple of a form. -/
def smulF (a : ℤ) (f : Form m) : Form m := fun k => (a * (f k).1, a * (f k).2)

/-- The zero form. -/
def zeroF : Form m := fun _ => (0, 0)

/-- Integer combination `Σ mᵢ lᵢ`. -/
def lcF : List ℤ → List (Form m) → Form m
  | a :: ms, c :: l => addF (smulF a c) (lcF ms l)
  | _, _ => zeroF

/-- Boolean equality of forms. -/
def eqF (f g : Form m) : Bool := (List.finRange m).all fun k => (f k).1 == (g k).1 && (f k).2 == (g k).2

/-- The difference form `x_k − y_k`. -/
def dform (k : Fin m) : Form m := fun j => if j = k then (1, -1) else (0, 0)

/-- Integer combination of values. -/
def lcvI : List ℤ → List ℤ → ℤ
  | a :: ms, y :: ys => a * y + lcvI ms ys
  | _, _ => 0

theorem eqF_iff {f g : Form m} : eqF f g = true ↔ f = g := by
  constructor
  · intro h
    funext k
    have hk := List.all_eq_true.mp h k (List.mem_finRange k)
    simp only [Bool.and_eq_true, beq_iff_eq] at hk
    exact Prod.ext hk.1 hk.2
  · rintro rfl
    exact List.all_eq_true.mpr fun k _ => by simp

theorem fval_addF (f g : Form m) (q : Fin m → ℤ × ℤ) : fval (addF f g) q = fval f q + fval g q := by
  simp only [fval, addF, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem fval_smulF (a : ℤ) (f : Form m) (q : Fin m → ℤ × ℤ) : fval (smulF a f) q = a * fval f q := by
  simp only [fval, smulF, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem fval_zeroF (q : Fin m → ℤ × ℤ) : fval (zeroF : Form m) q = 0 := by
  simp [fval, zeroF]

theorem fval_lcF (ms : List ℤ) (l : List (Form m)) (q : Fin m → ℤ × ℤ) :
    fval (lcF ms l) q = lcvI ms (l.map fun f => fval f q) := by
  induction ms generalizing l with
  | nil => cases l <;> simp [lcF, lcvI, fval_zeroF]
  | cons a ms ih =>
    cases l with
    | nil => simp [lcF, lcvI, fval_zeroF]
    | cons c l => simp only [lcF, lcvI, List.map_cons, fval_addF, fval_smulF, ih]

theorem fval_dform (k : Fin m) (q : Fin m → ℤ × ℤ) : fval (dform k) q = (q k).1 - (q k).2 := by
  simp only [fval, dform]
  rw [Finset.sum_eq_single k (fun j _ hj => by simp [hj]) (fun h => absurd (Finset.mem_univ k) h)]
  simp; ring

/-! ## Determination -/

/-- `l` determines the form `f` on the sample space. -/
def Det (Γ : Finset (ℤ × ℤ)) (l : List (Form m)) (f : Form m) : Prop :=
  ∃ φ : List ℤ → ℤ, ∀ q ∈ Om Γ m, φ (l.map fun c => fval c q) = fval f q

/-- **Mutual determination**: equal joint entropies. -/
theorem HLm_eq_of_det {Γ : Finset (ℤ × ℤ)} {l₁ l₂ : List (Form m)}
    (h₁₂ : ∀ f ∈ l₂, Det Γ l₁ f) (h₂₁ : ∀ f ∈ l₁, Det Γ l₂ f) : HLm Γ m l₁ = HLm Γ m l₂ := by
  classical
  refine pushEntropy_eq_of_comp (wt_nonneg Γ m)
    (fun y => l₂.map fun f => if h : Det Γ l₁ f then h.choose y else 0)
    (fun y => l₁.map fun f => if h : Det Γ l₂ f then h.choose y else 0) ?_ ?_
  · intro q hq
    refine List.map_congr_left fun f hf => ?_
    rw [dite_eq_left (h₁₂ f hf)]
    exact (h₁₂ f hf).choose_spec q hq
  · intro q hq
    refine List.map_congr_left fun f hf => ?_
    rw [dite_eq_left (h₂₁ f hf)]
    exact (h₂₁ f hf).choose_spec q hq

/-- **Determination from integer data.**  `c • f = Σ mᵢ lᵢ + g` with `c ≠ 0`, where every copy `k` used by `g`
has a witness with `wc k • (x_k − y_k) = Σ (wit k)ᵢ lᵢ`, `wc k ≠ 0`; then `l` determines `f` (distinct differences
in `Γ`; the divisions are exact over `ℤ` on the sample space). -/
theorem Det.gen {Γ : Finset (ℤ × ℤ)}
    (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q')
    {l : List (Form m)} {f : Form m} (c : ℤ) (hc : c ≠ 0) (ms : List ℤ) (g : Form m)
    (wc : Fin m → ℤ) (wit : Fin m → List ℤ)
    (hf : eqF (smulF c f) (addF (lcF ms l) g) = true)
    (hg : (List.finRange m).all (fun k => ((g k).1 == 0 && (g k).2 == 0) ||
      (wc k != 0 && eqF (lcF (wit k) l) (smulF (wc k) (dform k)))) = true) :
    Det Γ l f := by
  rw [eqF_iff] at hf
  refine ⟨fun y => (lcvI ms y + ∑ k, ((g k).1 * (rep Γ (lcvI (wit k) y / wc k)).1
      + (g k).2 * (rep Γ (lcvI (wit k) y / wc k)).2)) / c, fun q hq => ?_⟩
  have hqk := mem_Om.mp hq
  have key : ∀ k, (g k).1 * (rep Γ (lcvI (wit k) (l.map fun c => fval c q) / wc k)).1
      + (g k).2 * (rep Γ (lcvI (wit k) (l.map fun c => fval c q) / wc k)).2
      = (g k).1 * (q k).1 + (g k).2 * (q k).2 := by
    intro k
    have hk := List.all_eq_true.mp hg k (List.mem_finRange k)
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hk
    rcases hk with ⟨h1, h2⟩ | ⟨hw0, hw⟩
    · rw [h1, h2]; ring
    · rw [eqF_iff] at hw
      have hd : lcvI (wit k) (l.map fun c => fval c q) / wc k = (q k).1 - (q k).2 := by
        rw [← fval_lcF, hw, fval_smulF, fval_dform, Int.mul_ediv_cancel_left _ hw0]
      rw [hd, rep_eq hinj (hqk k)]
  have hsum : lcvI ms (l.map fun c => fval c q) + ∑ k, ((g k).1 * (rep Γ (lcvI (wit k)
      (l.map fun c => fval c q) / wc k)).1 + (g k).2 * (rep Γ (lcvI (wit k)
      (l.map fun c => fval c q) / wc k)).2) = c * fval f q := by
    rw [Finset.sum_congr rfl fun k _ => key k, ← fval_lcF]
    have := congrArg (fun h => fval h q) hf
    simp only [fval_smulF, fval_addF] at this
    rw [this]
    rfl
  simp only
  rw [hsum, Int.mul_ediv_cancel_left _ hc]

/-! ## Shannon facts -/

theorem HLm_pair (Γ : Finset (ℤ × ℤ)) (l₁ l₂ : List (Form m)) :
    pushEntropy (Om Γ m) (wt Γ m) (fun q => (l₁.map fun c => fval c q, l₂.map fun c => fval c q))
      = HLm Γ m (l₁ ++ l₂) := by
  refine pushEntropy_eq_of_comp (wt_nonneg Γ m) (fun x => x.1 ++ x.2)
    (fun y => (y.take l₁.length, y.drop l₁.length)) ?_ ?_
  · intro q _; simp [List.map_append]
  · intro q _
    simp only [List.map_append]
    refine Prod.ext ?_ ?_
    · simp
    · simp

theorem HLm_triple (Γ : Finset (ℤ × ℤ)) (l₁ l₂ l₃ : List (Form m)) :
    pushEntropy (Om Γ m) (wt Γ m) (fun q => (l₁.map fun c => fval c q, l₂.map fun c => fval c q,
      l₃.map fun c => fval c q)) = HLm Γ m (l₁ ++ l₂ ++ l₃) := by
  refine pushEntropy_eq_of_comp (wt_nonneg Γ m) (fun x => x.1 ++ x.2.1 ++ x.2.2)
    (fun y => (y.take l₁.length, (y.drop l₁.length).take l₂.length,
      y.drop (l₁.length + l₂.length))) ?_ ?_
  · intro q _; simp [List.map_append]
  · intro q _
    simp only [List.map_append, List.append_assoc]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · simp
    · simp
    · simp [List.drop_append]

/-- **Submodularity**: `H(A, B, C) + H(B) ≤ H(A, B) + H(B, C)`. -/
theorem HLm_submod {Γ : Finset (ℤ × ℤ)} (hΓ : Γ.Nonempty) (l₁ l₂ l₃ : List (Form m)) :
    HLm Γ m (l₁ ++ l₂ ++ l₃) + HLm Γ m l₂ ≤ HLm Γ m (l₁ ++ l₂) + HLm Γ m (l₂ ++ l₃) := by
  have h := pushEntropy_submodular (wt_nonneg Γ m) (wt_sum hΓ m) (fun q => l₁.map fun c => fval c q)
    (fun q => l₂.map fun c => fval c q) (fun q => l₃.map fun c => fval c q)
  rw [HLm_triple, HLm_pair, HLm_pair] at h
  exact h

/-- **Monotonicity**: adding forms does not decrease the joint entropy. -/
theorem HLm_mono (Γ : Finset (ℤ × ℤ)) (l₁ l₂ : List (Form m)) : HLm Γ m l₁ ≤ HLm Γ m (l₁ ++ l₂) := by
  have h := pushEntropy_comp_le (wt_nonneg Γ m) (fun q => (l₁ ++ l₂).map fun c => fval c q)
    (fun y => y.take l₁.length)
  simpa [HLm, List.map_append] using h

theorem HLm_nil {Γ : Finset (ℤ × ℤ)} (hΓ : Γ.Nonempty) : HLm Γ m [] = 0 := by
  classical
  refine le_antisymm ?_ (pushEntropy_nonneg (wt_nonneg Γ m) (wt_sum hΓ m))
  have := pushEntropy_le_log_card (s := Om Γ m) (p := wt Γ m)
    (f := fun q => ([] : List (Form m)).map fun c => fval c q) (t := {[]}) (wt_nonneg Γ m)
    (wt_sum hΓ m) (fun q _ => by simp)
  simpa [HLm] using this

theorem HLm_nonneg {Γ : Finset (ℤ × ℤ)} (hΓ : Γ.Nonempty) (l : List (Form m)) : 0 ≤ HLm Γ m l :=
  pushEntropy_nonneg (wt_nonneg Γ m) (wt_sum hΓ m)

/-- A member of `l` is determined by `l`. -/
theorem Det.mem {Γ : Finset (ℤ × ℤ)} {l : List (Form m)} {f : Form m} (hf : f ∈ l) : Det Γ l f := by
  classical
  refine ⟨fun y => ((l.zip y).lookup f).getD 0, fun q _ => ?_⟩
  exact lookup_zip_map (G := ℤ) l (fun c => fval c q) hf

end EntropyBounds.Iid
