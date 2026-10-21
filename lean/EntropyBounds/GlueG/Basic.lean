import EntropyBounds.Glue.Basic

/-!
# Configurations of glued copies of a pair, with values in an abelian group

The framework of `EntropyBounds.Glue` with vertices in `G × G` for an abelian group `G` (`Glue` is the case
`G = ℝ`).  A *configuration* `C : Conf N G` is a finite weighted sample space `(C.Ω, C.p)` carrying `N` vertices
`C.co i v ∈ G × G`.  Integer forms `f : Form N` are evaluated by `rval` (integer multiples in `G`), and
`C.H l = H((f(C.co i))_{f ∈ l})`.

* `Conf.H_eq_of_det`: lists that determine each other have equal entropies.  `checkDWR` verifies integer data for a
  determination modulo relations: `c • f = Σ mᵢ lᵢ + Σ rⱼ Rⱼ + g` where `g` may only use `x_k, y_k` when
  `wc_k • (x_k − y_k)` is a combination of `l` and the relations (`Γ` has distinct differences).  Unlike `Glue`,
  the multipliers `c` and `wc_k` must be powers of two (`isPow2`); `Det.gen` then needs only that doubling is
  injective on `G` (`h2 : ∀ x : G, x + x = 0 → x = 0`).
* `Conf.H_submod`, `Conf.H_mono`, `Conf.H_nil`, `Conf.H_nonneg`: Shannon facts.
-/

open Finset

namespace EntropyBounds.GlueG

open SumsDifferences SumsDifferences.CoupledEntropy SumsDifferences.CoupledForms EntropyBounds.Iid

variable {N : ℕ} {G : Type} [AddCommGroup G]

/-- The value of an integer form at a point with coordinates in `G`. -/
def rval (f : Form N) (q : Fin N → G × G) : G :=
  ∑ k, ((f k).1 • (q k).1 + (f k).2 • (q k).2)

/-- A finite weighted sample space carrying `N` vertices in `G × G`. -/
structure Conf (N : ℕ) (G : Type) where
  ι : Type
  Ω : Finset ι
  p : ι → ℝ
  co : ι → Fin N → G × G

namespace Conf

variable [DecidableEq G]

/-- Joint entropy of a list of forms. -/
noncomputable def H (C : Conf N G) (l : List (Form N)) : ℝ :=
  pushEntropy C.Ω C.p (fun i => l.map fun f => rval f (C.co i))

/-- The standing hypotheses: a probability weight, and every vertex in `Γ`. -/
structure Valid (C : Conf N G) (Γ : Finset (G × G)) : Prop where
  nonneg : ∀ i ∈ C.Ω, 0 ≤ C.p i
  sum_one : ∑ i ∈ C.Ω, C.p i = 1
  mem : ∀ i ∈ C.Ω, ∀ v, C.co i v ∈ Γ

/-- `r` vanishes on the sample space. -/
def Rel (C : Conf N G) (r : Form N) : Prop := ∀ i ∈ C.Ω, rval r (C.co i) = 0

/-- `l` determines `f` on the sample space. -/
def Det (C : Conf N G) (l : List (Form N)) (f : Form N) : Prop :=
  ∃ φ : List G → G, ∀ i ∈ C.Ω, φ (l.map fun c => rval c (C.co i)) = rval f (C.co i)

end Conf

/-! ## Values of computable form arithmetic -/

/-- Integer combination of values in `G`. -/
def lcvG : List ℤ → List G → G
  | a :: ms, y :: ys => a • y + lcvG ms ys
  | _, _ => 0

theorem rval_addF (f g : Form N) (q : Fin N → G × G) : rval (addF f g) q = rval f q + rval g q := by
  simp only [rval, addF, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by simp only [add_smul]; abel

theorem rval_smulF (a : ℤ) (f : Form N) (q : Fin N → G × G) : rval (smulF a f) q = a • rval f q := by
  simp only [rval, smulF, Finset.smul_sum]
  exact Finset.sum_congr rfl fun k _ => by simp only [smul_add, mul_smul]

theorem rval_zeroF (q : Fin N → G × G) : rval (zeroF : Form N) q = 0 := by
  simp [rval, zeroF]

theorem rval_lcF (ms : List ℤ) (l : List (Form N)) (q : Fin N → G × G) :
    rval (lcF ms l) q = lcvG ms (l.map fun f => rval f q) := by
  induction ms generalizing l with
  | nil => cases l <;> simp [lcF, lcvG, rval_zeroF]
  | cons a ms ih =>
    cases l with
    | nil => simp [lcF, lcvG, rval_zeroF]
    | cons c l => simp only [lcF, lcvG, List.map_cons, rval_addF, rval_smulF, ih]

theorem rval_dform (k : Fin N) (q : Fin N → G × G) : rval (dform k) q = (q k).1 - (q k).2 := by
  simp only [rval, dform]
  rw [Finset.sum_eq_single k (fun j _ hj => by simp [hj]) (fun h => absurd (Finset.mem_univ k) h)]
  simp [sub_eq_add_neg]

theorem lcvG_zero (ms : List ℤ) (ys : List G) (h : ∀ y ∈ ys, y = 0) : lcvG ms ys = 0 := by
  induction ms generalizing ys with
  | nil => cases ys <;> rfl
  | cons a ms ih =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      simp only [lcvG]
      rw [h y List.mem_cons_self, ih ys fun z hz => h z (List.mem_cons_of_mem _ hz)]
      simp

/-! ## Powers of two -/

/-- `n` is a power of two (halving, with fuel `k`). -/
def pow2F : ℕ → ℕ → Bool
  | 0, n => n == 1
  | k + 1, n => n == 1 || (n % 2 == 0 && n != 0 && pow2F k (n / 2))

/-- `c` is a (positive) power of two. -/
def isPow2 (c : ℤ) : Bool :=
  match c with
  | .ofNat n => pow2F 64 n
  | .negSucc _ => false

theorem pow2F_spec : ∀ (k n : ℕ), pow2F k n = true → ∃ a : ℕ, n = 2 ^ a
  | 0, n, h => ⟨0, by simpa [pow2F] using h⟩
  | k + 1, n, h => by
    simp only [pow2F, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    rcases h with h | ⟨⟨h2, _⟩, hk⟩
    · exact ⟨0, by simpa using h⟩
    · obtain ⟨a, ha⟩ := pow2F_spec k (n / 2) hk
      refine ⟨a + 1, ?_⟩
      rw [pow_succ, ← ha]
      omega

theorem isPow2_spec {c : ℤ} (h : isPow2 c = true) : ∃ a : ℕ, c = 2 ^ a := by
  match c, h with
  | .ofNat n, h =>
    obtain ⟨a, ha⟩ := pow2F_spec 64 n h
    exact ⟨a, by rw [ha]; push_cast; rfl⟩

/-- Multiplication by a power of two is injective when doubling is. -/
theorem smul_pow2_injective (h2 : ∀ x : G, x + x = 0 → x = 0) {c : ℤ} (hc : isPow2 c = true) :
    Function.Injective (fun x : G => c • x) := by
  obtain ⟨a, rfl⟩ := isPow2_spec hc
  have hz : ∀ (a : ℕ) (x : G), ((2 : ℤ) ^ a) • x = 0 → x = 0 := by
    intro a
    induction a with
    | zero => intro x hx; simpa using hx
    | succ a ih =>
      intro x hx
      apply h2
      apply ih
      rw [pow_succ, mul_smul, two_smul] at hx
      exact hx
  intro x y hxy
  simp only at hxy
  have := hz a (x - y) (by rw [smul_sub, hxy, sub_self])
  exact sub_eq_zero.mp this

/-- The solution `u` of `c • u = t` when it exists (`0` otherwise). -/
noncomputable def divG (c : ℤ) (t : G) : G :=
  open Classical in if h : ∃ u : G, c • u = t then h.choose else 0

theorem divG_eq (h2 : ∀ x : G, x + x = 0 → x = 0) {c : ℤ} (hc : isPow2 c = true) (u : G) :
    divG c (c • u) = u := by
  have hex : ∃ v : G, c • v = c • u := ⟨u, rfl⟩
  unfold divG
  rw [dite_eq_left hex]
  exact smul_pow2_injective h2 hc hex.choose_spec

namespace Conf

variable [DecidableEq G] {C : Conf N G}

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

/-- **Determination from integer data, modulo relations** (multipliers powers of two). -/
theorem Det.gen (h2 : ∀ x : G, x + x = 0 → x = 0) {Γ : Finset (G × G)}
    (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q')
    (hmem : ∀ i ∈ C.Ω, ∀ v, C.co i v ∈ Γ) {R : List (Form N)} (hR : ∀ r ∈ R, C.Rel r)
    {l : List (Form N)} {f : Form N} (c : ℤ) (hc : isPow2 c = true) (ms rs : List ℤ) (g : Form N)
    (wc : Fin N → ℤ) (wit wr : Fin N → List ℤ)
    (hf : eqF (smulF c f) (addF (addF (lcF ms l) (lcF rs R)) g) = true)
    (hg : (List.finRange N).all (fun k => ((g k).1 == 0 && (g k).2 == 0) ||
      (isPow2 (wc k) && eqF (addF (lcF (wit k) l) (lcF (wr k) R)) (smulF (wc k) (dform k)))) = true) :
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
        rw [this, divG_eq h2 hw0]
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
  rw [hsum, divG_eq h2 hc]

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

/-- Check one witness for `f` from `l` modulo the relations `R` (multipliers powers of two). -/
def checkDWR (R l : List (Form N)) (f : Form N) (w : EntropyBounds.Glue.DWR N) : Bool :=
  isPow2 w.c && eqF (smulF w.c f) (addF (addF (lcF w.ms l) (lcF w.rs R)) w.g) &&
    (List.finRange N).all (fun k => ((w.g k).1 == 0 && (w.g k).2 == 0) ||
      (isPow2 (w.wc k) && eqF (addF (lcF (w.wit k) l) (lcF (w.wr k) R)) (smulF (w.wc k) (dform k))))

/-- Check witnesses for every form of `l₂` from `l₁`. -/
def checkDWRs (R l₁ l₂ : List (Form N)) (ws : List (EntropyBounds.Glue.DWR N)) : Bool :=
  ws.length == l₂.length && (l₂.zip ws).all (fun p => checkDWR R l₁ p.1 p.2)

namespace Conf

variable [DecidableEq G] {C : Conf N G} {Γ : Finset (G × G)}

theorem det_of_checkDWR (h2 : ∀ x : G, x + x = 0 → x = 0)
    (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') (hv : C.Valid Γ)
    {R : List (Form N)} (hR : ∀ r ∈ R, C.Rel r) {l : List (Form N)} {f : Form N} {w : EntropyBounds.Glue.DWR N}
    (h : checkDWR R l f w = true) : C.Det l f := by
  simp only [checkDWR, Bool.and_eq_true] at h
  obtain ⟨⟨hc, hf⟩, hg⟩ := h
  exact Det.gen h2 hinj hv.mem hR w.c hc w.ms w.rs w.g w.wc w.wit w.wr hf hg

theorem det_of_checkDWRs (h2 : ∀ x : G, x + x = 0 → x = 0)
    (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') (hv : C.Valid Γ)
    {R : List (Form N)} (hR : ∀ r ∈ R, C.Rel r) {l₁ l₂ : List (Form N)} {ws : List (EntropyBounds.Glue.DWR N)}
    (h : checkDWRs R l₁ l₂ ws = true) : ∀ f ∈ l₂, C.Det l₁ f := by
  simp only [checkDWRs, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hlen, hall⟩ := h
  intro f hf
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hf
  have hi' : i < ws.length := hlen ▸ hi
  have hmem : (l₂[i], ws[i]) ∈ l₂.zip ws := by
    rw [List.mem_iff_getElem]
    exact ⟨i, by simp [hi, hi'], by simp⟩
  exact det_of_checkDWR h2 hinj hv hR (List.all_eq_true.mp hall _ hmem)

/-- **Identity from witnesses.** -/
theorem H_eq_wit (h2 : ∀ x : G, x + x = 0 → x = 0)
    (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') (hv : C.Valid Γ)
    {R : List (Form N)} (hR : ∀ r ∈ R, C.Rel r) (l₁ l₂ : List (Form N)) (w₁₂ w₂₁ : List (EntropyBounds.Glue.DWR N))
    (h₁₂ : checkDWRs R l₁ l₂ w₁₂ = true) (h₂₁ : checkDWRs R l₂ l₁ w₂₁ = true) : C.H l₁ = C.H l₂ :=
  H_eq_of_det hv.nonneg (det_of_checkDWRs h2 hinj hv hR h₁₂) (det_of_checkDWRs h2 hinj hv hR h₂₁)

/-- `C.H l = 0` when every form of `l` is determined by the empty list. -/
theorem H_eq_zero_wit (h2 : ∀ x : G, x + x = 0 → x = 0)
    (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') (hv : C.Valid Γ)
    {R : List (Form N)} (hR : ∀ r ∈ R, C.Rel r) (l : List (Form N)) (w : List (EntropyBounds.Glue.DWR N))
    (h : checkDWRs R [] l w = true) : C.H l = 0 := by
  rw [← H_nil hv.nonneg hv.sum_one]
  exact H_eq_of_det hv.nonneg (fun f hf => absurd hf List.not_mem_nil) (det_of_checkDWRs h2 hinj hv hR h)

end Conf

end EntropyBounds.GlueG
