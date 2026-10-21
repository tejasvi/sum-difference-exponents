import EntropyBounds.Iid.Witness

/-!
# Configurations of glued copies of a pair (the model behind GGSTW 6.30(a))

A *configuration* `C : Conf N` is a finite weighted sample space `(C.Ω, C.p)` carrying `N` vertices
`C.co i v ∈ ℝ × ℝ` (coordinates `x_v`, `y_v`).  Integer forms `f : Form N` are evaluated by `rval`, and

  `C.H l = H((f(C.co i))_{f ∈ l})`

is the joint entropy of a list of forms.  A configuration is *valid* for `Γ` (`Conf.Valid`) when `C.p` is a
probability weight on `C.Ω` and every vertex takes values in `Γ`; a form `r` is a *relation* (`Conf.Rel`) when it
vanishes on `C.Ω`.

* `Conf.H_eq_of_det`: lists that determine each other have equal entropies.  `checkDWR` verifies integer data for a
  determination modulo relations: `c • f = Σ mᵢ lᵢ + Σ rⱼ Rⱼ + g` with `c ≠ 0`, where `g` may only use `x_k, y_k`
  when `x_k − y_k` is (up to a nonzero integer factor) a combination of `l` and the relations (`Γ` has distinct
  differences).  Divisions are exact in `ℝ`.
* `Conf.H_submod`, `Conf.H_mono`, `Conf.H_nil`, `Conf.H_nonneg`: Shannon facts.
-/

open Finset

namespace EntropyBounds.Glue

open SumsDifferences SumsDifferences.CoupledEntropy SumsDifferences.CoupledForms EntropyBounds.Iid

variable {N : ℕ}

/-- The value of an integer form at a point with real coordinates. -/
noncomputable def rval (f : Form N) (q : Fin N → ℝ × ℝ) : ℝ :=
  ∑ k, (((f k).1 : ℝ) * (q k).1 + ((f k).2 : ℝ) * (q k).2)

/-- A finite weighted sample space carrying `N` vertices. -/
structure Conf (N : ℕ) where
  ι : Type
  Ω : Finset ι
  p : ι → ℝ
  co : ι → Fin N → ℝ × ℝ

namespace Conf

/-- Joint entropy of a list of forms. -/
noncomputable def H (C : Conf N) (l : List (Form N)) : ℝ :=
  pushEntropy C.Ω C.p (fun i => l.map fun f => rval f (C.co i))

/-- The standing hypotheses: a probability weight, and every vertex in `Γ`. -/
structure Valid (C : Conf N) (Γ : Finset (ℝ × ℝ)) : Prop where
  nonneg : ∀ i ∈ C.Ω, 0 ≤ C.p i
  sum_one : ∑ i ∈ C.Ω, C.p i = 1
  mem : ∀ i ∈ C.Ω, ∀ v, C.co i v ∈ Γ

/-- `r` vanishes on the sample space. -/
def Rel (C : Conf N) (r : Form N) : Prop := ∀ i ∈ C.Ω, rval r (C.co i) = 0

/-- `l` determines `f` on the sample space. -/
def Det (C : Conf N) (l : List (Form N)) (f : Form N) : Prop :=
  ∃ φ : List ℝ → ℝ, ∀ i ∈ C.Ω, φ (l.map fun c => rval c (C.co i)) = rval f (C.co i)

end Conf

/-! ## Values of computable form arithmetic -/

/-- Integer combination of real values. -/
noncomputable def lcvR : List ℤ → List ℝ → ℝ
  | a :: ms, y :: ys => (a : ℝ) * y + lcvR ms ys
  | _, _ => 0

theorem rval_addF (f g : Form N) (q : Fin N → ℝ × ℝ) : rval (addF f g) q = rval f q + rval g q := by
  simp only [rval, addF, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by push_cast; ring

theorem rval_smulF (a : ℤ) (f : Form N) (q : Fin N → ℝ × ℝ) : rval (smulF a f) q = a * rval f q := by
  simp only [rval, smulF, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by push_cast; ring

theorem rval_zeroF (q : Fin N → ℝ × ℝ) : rval (zeroF : Form N) q = 0 := by
  simp [rval, zeroF]

theorem rval_lcF (ms : List ℤ) (l : List (Form N)) (q : Fin N → ℝ × ℝ) :
    rval (lcF ms l) q = lcvR ms (l.map fun f => rval f q) := by
  induction ms generalizing l with
  | nil => cases l <;> simp [lcF, lcvR, rval_zeroF]
  | cons a ms ih =>
    cases l with
    | nil => simp [lcF, lcvR, rval_zeroF]
    | cons c l => simp only [lcF, lcvR, List.map_cons, rval_addF, rval_smulF, ih]

theorem rval_dform (k : Fin N) (q : Fin N → ℝ × ℝ) : rval (dform k) q = (q k).1 - (q k).2 := by
  simp only [rval, dform]
  rw [Finset.sum_eq_single k (fun j _ hj => by simp [hj]) (fun h => absurd (Finset.mem_univ k) h)]
  simp; ring

theorem lcvR_zero (ms : List ℤ) (ys : List ℝ) (h : ∀ y ∈ ys, y = 0) : lcvR ms ys = 0 := by
  induction ms generalizing ys with
  | nil => cases ys <;> rfl
  | cons a ms ih =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      simp only [lcvR]
      rw [h y List.mem_cons_self, ih ys fun z hz => h z (List.mem_cons_of_mem _ hz)]
      ring

namespace Conf

variable {C : Conf N}

/-! ## Determination -/

/-- **Mutual determination**: equal joint entropies. -/
theorem H_eq_of_det (hp : ∀ i ∈ C.Ω, 0 ≤ C.p i) {l₁ l₂ : List (Form N)}
    (h₁₂ : ∀ f ∈ l₂, C.Det l₁ f) (h₂₁ : ∀ f ∈ l₁, C.Det l₂ f) : C.H l₁ = C.H l₂ := by
  classical
  refine pushEntropy_eq_of_comp hp
    (fun y => l₂.map fun f => if h : C.Det l₁ f then h.choose y else 0)
    (fun y => l₁.map fun f => if h : C.Det l₂ f then h.choose y else 0) ?_ ?_
  · intro i hi
    refine List.map_congr_left fun f hf => ?_
    rw [dite_eq_left (h₁₂ f hf)]
    exact (h₁₂ f hf).choose_spec i hi
  · intro i hi
    refine List.map_congr_left fun f hf => ?_
    rw [dite_eq_left (h₂₁ f hf)]
    exact (h₂₁ f hf).choose_spec i hi

/-- Relations evaluate to `0` on the sample space. -/
theorem rel_vals {R : List (Form N)} (hR : ∀ r ∈ R, C.Rel r) {i : C.ι} (hi : i ∈ C.Ω) :
    ∀ y ∈ R.map (fun r => rval r (C.co i)), y = 0 := by
  intro y hy
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hy
  exact hR r hr i hi

/-- **Determination from integer data, modulo relations.** -/
theorem Det.gen {Γ : Finset (ℝ × ℝ)} (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q')
    (hmem : ∀ i ∈ C.Ω, ∀ v, C.co i v ∈ Γ) {R : List (Form N)} (hR : ∀ r ∈ R, C.Rel r)
    {l : List (Form N)} {f : Form N} (c : ℤ) (hc : c ≠ 0) (ms rs : List ℤ) (g : Form N)
    (wc : Fin N → ℤ) (wit wr : Fin N → List ℤ)
    (hf : eqF (smulF c f) (addF (addF (lcF ms l) (lcF rs R)) g) = true)
    (hg : (List.finRange N).all (fun k => ((g k).1 == 0 && (g k).2 == 0) ||
      (wc k != 0 && eqF (addF (lcF (wit k) l) (lcF (wr k) R)) (smulF (wc k) (dform k)))) = true) :
    C.Det l f := by
  rw [eqF_iff] at hf
  refine ⟨fun y => (lcvR ms y + ∑ k, (((g k).1 : ℝ) * (rep Γ (lcvR (wit k) y / wc k)).1
      + ((g k).2 : ℝ) * (rep Γ (lcvR (wit k) y / wc k)).2)) / c, fun i hi => ?_⟩
  have hRz : lcvR rs (R.map fun r => rval r (C.co i)) = 0 := lcvR_zero _ _ (rel_vals hR hi)
  have key : ∀ k, ((g k).1 : ℝ) * (rep Γ (lcvR (wit k) (l.map fun c => rval c (C.co i)) / wc k)).1
      + ((g k).2 : ℝ) * (rep Γ (lcvR (wit k) (l.map fun c => rval c (C.co i)) / wc k)).2
      = ((g k).1 : ℝ) * (C.co i k).1 + ((g k).2 : ℝ) * (C.co i k).2 := by
    intro k
    have hk := List.all_eq_true.mp hg k (List.mem_finRange k)
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hk
    rcases hk with ⟨h1, h2⟩ | ⟨hw0, hw⟩
    · rw [h1, h2]; simp
    · rw [eqF_iff] at hw
      have hwR : ((wc k : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hw0
      have hd : lcvR (wit k) (l.map fun c => rval c (C.co i)) / wc k = (C.co i k).1 - (C.co i k).2 := by
        have := congrArg (fun h => rval h (C.co i)) hw
        simp only [rval_addF, rval_lcF, rval_smulF, rval_dform] at this
        rw [lcvR_zero (wr k) _ (rel_vals hR hi), add_zero] at this
        rw [this, mul_div_cancel_left₀ _ hwR]
      rw [hd, rep_eq hinj (hmem i hi k)]
  have hsum : lcvR ms (l.map fun c => rval c (C.co i)) + ∑ k, (((g k).1 : ℝ) * (rep Γ (lcvR (wit k)
      (l.map fun c => rval c (C.co i)) / wc k)).1 + ((g k).2 : ℝ) * (rep Γ (lcvR (wit k)
      (l.map fun c => rval c (C.co i)) / wc k)).2) = c * rval f (C.co i) := by
    rw [Finset.sum_congr rfl fun k _ => key k, ← rval_lcF]
    have := congrArg (fun h => rval h (C.co i)) hf
    simp only [rval_smulF, rval_addF] at this
    rw [this, rval_lcF rs R, hRz, add_zero]
    rfl
  have hcR : ((c : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hc
  simp only
  rw [hsum, mul_div_cancel_left₀ _ hcR]

/-! ## Shannon facts -/

theorem H_pair (hp : ∀ i ∈ C.Ω, 0 ≤ C.p i) (l₁ l₂ : List (Form N)) :
    pushEntropy C.Ω C.p (fun i => (l₁.map fun c => rval c (C.co i), l₂.map fun c => rval c (C.co i)))
      = C.H (l₁ ++ l₂) := by
  refine pushEntropy_eq_of_comp hp (fun x => x.1 ++ x.2)
    (fun y => (y.take l₁.length, y.drop l₁.length)) ?_ ?_
  · intro q _; simp [List.map_append]
  · intro q _
    simp only [List.map_append]
    refine Prod.ext ?_ ?_
    · simp
    · simp

theorem H_triple (hp : ∀ i ∈ C.Ω, 0 ≤ C.p i) (l₁ l₂ l₃ : List (Form N)) :
    pushEntropy C.Ω C.p (fun i => (l₁.map fun c => rval c (C.co i), l₂.map fun c => rval c (C.co i),
      l₃.map fun c => rval c (C.co i))) = C.H (l₁ ++ l₂ ++ l₃) := by
  refine pushEntropy_eq_of_comp hp (fun x => x.1 ++ x.2.1 ++ x.2.2)
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
theorem H_submod (hp : ∀ i ∈ C.Ω, 0 ≤ C.p i) (hs : ∑ i ∈ C.Ω, C.p i = 1) (l₁ l₂ l₃ : List (Form N)) :
    C.H (l₁ ++ l₂ ++ l₃) + C.H l₂ ≤ C.H (l₁ ++ l₂) + C.H (l₂ ++ l₃) := by
  have h := pushEntropy_submodular hp hs (fun i => l₁.map fun c => rval c (C.co i))
    (fun i => l₂.map fun c => rval c (C.co i)) (fun i => l₃.map fun c => rval c (C.co i))
  rw [H_triple hp, H_pair hp, H_pair hp] at h
  exact h

/-- **Monotonicity**. -/
theorem H_mono (hp : ∀ i ∈ C.Ω, 0 ≤ C.p i) (l₁ l₂ : List (Form N)) : C.H l₁ ≤ C.H (l₁ ++ l₂) := by
  have h := pushEntropy_comp_le hp (fun i => (l₁ ++ l₂).map fun c => rval c (C.co i))
    (fun y => y.take l₁.length)
  simpa [H, List.map_append] using h

theorem H_nil (hp : ∀ i ∈ C.Ω, 0 ≤ C.p i) (hs : ∑ i ∈ C.Ω, C.p i = 1) : C.H [] = 0 := by
  classical
  refine le_antisymm ?_ (pushEntropy_nonneg hp hs)
  have := pushEntropy_le_log_card (s := C.Ω) (p := C.p)
    (f := fun i => ([] : List (Form N)).map fun c => rval c (C.co i)) (t := {[]}) hp hs (fun q _ => by simp)
  simpa [H] using this

theorem H_nonneg (hp : ∀ i ∈ C.Ω, 0 ≤ C.p i) (hs : ∑ i ∈ C.Ω, C.p i = 1) (l : List (Form N)) : 0 ≤ C.H l :=
  pushEntropy_nonneg hp hs

end Conf

/-! ## Checkable witnesses -/

/-- A determination witness modulo relations. -/
structure DWR (N : ℕ) where
  c : ℤ
  ms : List ℤ
  rs : List ℤ
  g : Form N
  wc : Fin N → ℤ
  wit : Fin N → List ℤ
  wr : Fin N → List ℤ

/-- Check one witness for `f` from `l` modulo the relations `R`. -/
def checkDWR (R l : List (Form N)) (f : Form N) (w : DWR N) : Bool :=
  w.c != 0 && eqF (smulF w.c f) (addF (addF (lcF w.ms l) (lcF w.rs R)) w.g) &&
    (List.finRange N).all (fun k => ((w.g k).1 == 0 && (w.g k).2 == 0) ||
      (w.wc k != 0 && eqF (addF (lcF (w.wit k) l) (lcF (w.wr k) R)) (smulF (w.wc k) (dform k))))

/-- Check witnesses for every form of `l₂` from `l₁`. -/
def checkDWRs (R l₁ l₂ : List (Form N)) (ws : List (DWR N)) : Bool :=
  ws.length == l₂.length && (l₂.zip ws).all (fun p => checkDWR R l₁ p.1 p.2)

namespace Conf

variable {C : Conf N} {Γ : Finset (ℝ × ℝ)}

theorem det_of_checkDWR (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') (hv : C.Valid Γ)
    {R : List (Form N)} (hR : ∀ r ∈ R, C.Rel r) {l : List (Form N)} {f : Form N} {w : DWR N}
    (h : checkDWR R l f w = true) : C.Det l f := by
  simp only [checkDWR, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨hc, hf⟩, hg⟩ := h
  exact Det.gen hinj hv.mem hR w.c hc w.ms w.rs w.g w.wc w.wit w.wr hf hg

theorem det_of_checkDWRs (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') (hv : C.Valid Γ)
    {R : List (Form N)} (hR : ∀ r ∈ R, C.Rel r) {l₁ l₂ : List (Form N)} {ws : List (DWR N)}
    (h : checkDWRs R l₁ l₂ ws = true) : ∀ f ∈ l₂, C.Det l₁ f := by
  simp only [checkDWRs, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hlen, hall⟩ := h
  intro f hf
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hf
  have hi' : i < ws.length := hlen ▸ hi
  have hmem : (l₂[i], ws[i]) ∈ l₂.zip ws := by
    rw [List.mem_iff_getElem]
    exact ⟨i, by simp [hi, hi'], by simp⟩
  exact det_of_checkDWR hinj hv hR (List.all_eq_true.mp hall _ hmem)

/-- **Identity from witnesses.** -/
theorem H_eq_wit (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') (hv : C.Valid Γ)
    {R : List (Form N)} (hR : ∀ r ∈ R, C.Rel r) (l₁ l₂ : List (Form N)) (w₁₂ w₂₁ : List (DWR N))
    (h₁₂ : checkDWRs R l₁ l₂ w₁₂ = true) (h₂₁ : checkDWRs R l₂ l₁ w₂₁ = true) : C.H l₁ = C.H l₂ :=
  H_eq_of_det hv.nonneg (det_of_checkDWRs hinj hv hR h₁₂) (det_of_checkDWRs hinj hv hR h₂₁)

/-- `C.H l = 0` when every form of `l` is determined by the empty list. -/
theorem H_eq_zero_wit (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') (hv : C.Valid Γ)
    {R : List (Form N)} (hR : ∀ r ∈ R, C.Rel r) (l : List (Form N)) (w : List (DWR N))
    (h : checkDWRs R [] l w = true) : C.H l = 0 := by
  rw [← H_nil hv.nonneg hv.sum_one]
  exact H_eq_of_det hv.nonneg (fun f hf => absurd hf List.not_mem_nil) (det_of_checkDWRs hinj hv hR h)

end Conf

end EntropyBounds.Glue
