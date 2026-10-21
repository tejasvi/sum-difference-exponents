import EntropyBounds.Iid.Basic

/-!
# Independence of disjoint groups of copies, single-copy laws, and permutations of copies

For a set `A` of copies, `splitE A` identifies `Γ^m` with `Γ^A × Γ^{Aᶜ}`; under it the uniform law is the product of
the uniform laws (`wt_split`), so random variables that depend on disjoint groups of copies are independent:

* `pushEntropy_split`, `pushEntropy_split_fst`, `pushEntropy_split_snd`: entropy of a pair / of one side;
* `HLm_indep`: `H(l₁, l₂) = H(l₁) + H(l₂)` when the forms of `l₁` only use copies in `A` and those of `l₂` only
  copies outside `A` (Boolean form `HLm_indepB`);
* `pushWeight_single`: a function of one copy `q k` has the law of the same function under the uniform law on `Γ`;
  `HLm_pairK`: `H(x_k, y_k) = log #Γ`;
* `HLm_perm`: the joint entropy is invariant under any permutation of the copies.
-/

open Finset

namespace EntropyBounds.Iid

open SumsDifferences SumsDifferences.CoupledEntropy SumsDifferences.CoupledForms

variable {m : ℕ}

/-! ## Reindexing of laws -/

theorem pushWeight_reindex {ι ι' α : Type*} [DecidableEq ι'] [DecidableEq α] {Ω : Finset ι} {p : ι → ℝ} {p' : ι' → ℝ}
    (e : ι → ι') (he : Set.InjOn e Ω) (hp : ∀ i ∈ Ω, p' (e i) = p i) (φ : ι' → α) (a : α) :
    pushWeight Ω p (fun i => φ (e i)) a = pushWeight (Ω.image e) p' φ a := by
  classical
  simp only [pushWeight]
  rw [Finset.filter_image, Finset.sum_image (fun x hx y hy hxy =>
    he (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 hxy)]
  exact Finset.sum_congr rfl fun i hi => (hp i (Finset.mem_filter.mp hi).1).symm

/-! ## Splitting the copies -/

section Split

variable (Γ : Finset (ℤ × ℤ))

/-- The uniform law on `Γ^{p}` for a set of copies given by a predicate. -/
def OmS (p : Fin m → Prop) [DecidablePred p] : Finset ({k // p k} → ℤ × ℤ) :=
  Fintype.piFinset (fun _ => Γ)

noncomputable def wtS (p : Fin m → Prop) [DecidablePred p] : ({k // p k} → ℤ × ℤ) → ℝ :=
  fun _ => ((#Γ : ℝ)⁻¹) ^ Fintype.card {k // p k}

variable {Γ}

theorem wtS_nonneg (p : Fin m → Prop) [DecidablePred p] : ∀ r ∈ OmS Γ p, 0 ≤ wtS Γ p r :=
  fun _ _ => by unfold wtS; positivity

theorem wtS_sum (hΓ : Γ.Nonempty) (p : Fin m → Prop) [DecidablePred p] :
    ∑ r ∈ OmS Γ p, wtS Γ p r = 1 := by
  have h : (0 : ℝ) < #Γ := by exact_mod_cast hΓ.card_pos
  simp only [wtS, OmS, Finset.sum_const, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ,
    nsmul_eq_mul, Nat.cast_pow]
  rw [inv_pow, mul_inv_cancel₀ (by positivity)]

/-- The splitting `Γ^m ≃ Γ^{p} × Γ^{¬p}`. -/
abbrev splitE (p : Fin m → Prop) [DecidablePred p] :
    (Fin m → ℤ × ℤ) ≃ ({k // p k} → ℤ × ℤ) × ({k // ¬ p k} → ℤ × ℤ) :=
  Equiv.piEquivPiSubtypeProd p (fun _ => ℤ × ℤ)

theorem image_split (p : Fin m → Prop) [DecidablePred p] :
    (Om Γ m).image (splitE p) = OmS Γ p ×ˢ OmS Γ (fun k => ¬ p k) := by
  ext ⟨r₁, r₂⟩
  simp only [Finset.mem_image, Finset.mem_product, OmS, Fintype.mem_piFinset, Om]
  constructor
  · rintro ⟨q, hq, hqe⟩
    rw [Equiv.piEquivPiSubtypeProd_apply, Prod.mk.injEq] at hqe
    obtain ⟨rfl, rfl⟩ := hqe
    exact ⟨fun k => hq k, fun k => hq k⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨(splitE p).symm (r₁, r₂), fun k => ?_, (splitE p).apply_symm_apply _⟩
    rw [Equiv.piEquivPiSubtypeProd_symm_apply]
    split_ifs with h
    · exact h₁ ⟨k, h⟩
    · exact h₂ ⟨k, h⟩

theorem wt_split (p : Fin m → Prop) [DecidablePred p] (q : Fin m → ℤ × ℤ) :
    productLaw (wtS Γ p) (wtS Γ (fun k => ¬ p k)) (splitE p q) = wt Γ m q := by
  simp only [productLaw, wtS, wt]
  rw [← pow_add]
  congr 1
  rw [Fintype.card_subtype, Fintype.card_subtype, Finset.card_filter_add_card_filter_not,
    Finset.card_univ, Fintype.card_fin]

theorem pushEntropy_split (hΓ : Γ.Nonempty) (p : Fin m → Prop) [DecidablePred p] {α β : Type*}
    [DecidableEq α] [DecidableEq β] (F₁ : ({k // p k} → ℤ × ℤ) → α) (F₂ : ({k // ¬ p k} → ℤ × ℤ) → β) :
    pushEntropy (Om Γ m) (wt Γ m) (fun q => (F₁ (splitE p q).1, F₂ (splitE p q).2))
      = pushEntropy (OmS Γ p) (wtS Γ p) F₁ + pushEntropy (OmS Γ (fun k => ¬ p k)) (wtS Γ (fun k => ¬ p k)) F₂ := by
  have h := pushEntropy_reindex (Ω := Om Γ m) (splitE p) (Equiv.injective _).injOn
    (p' := productLaw (wtS Γ p) (wtS Γ (fun k => ¬ p k))) (fun q _ => wt_split p q)
    (fun z => (F₁ z.1, F₂ z.2))
  rw [h, image_split]
  exact pushEntropy_productLaw_pair (wtS_nonneg _) (wtS_nonneg _) (wtS_sum hΓ _) (wtS_sum hΓ _) F₁ F₂

theorem pushEntropy_split_fst (hΓ : Γ.Nonempty) (p : Fin m → Prop) [DecidablePred p] {α : Type*}
    [DecidableEq α] (F₁ : ({k // p k} → ℤ × ℤ) → α) :
    pushEntropy (Om Γ m) (wt Γ m) (fun q => F₁ (splitE p q).1) = pushEntropy (OmS Γ p) (wtS Γ p) F₁ := by
  have h := pushEntropy_reindex (Ω := Om Γ m) (splitE p) (Equiv.injective _).injOn
    (p' := productLaw (wtS Γ p) (wtS Γ (fun k => ¬ p k))) (fun q _ => wt_split p q) (fun z => F₁ z.1)
  rw [h, image_split]
  exact pushEntropy_productLaw_fst (wtS_nonneg _) (wtS_nonneg _) (wtS_sum hΓ _) (wtS_sum hΓ _) F₁

theorem pushEntropy_split_snd (hΓ : Γ.Nonempty) (p : Fin m → Prop) [DecidablePred p] {β : Type*}
    [DecidableEq β] (F₂ : ({k // ¬ p k} → ℤ × ℤ) → β) :
    pushEntropy (Om Γ m) (wt Γ m) (fun q => F₂ (splitE p q).2)
      = pushEntropy (OmS Γ (fun k => ¬ p k)) (wtS Γ (fun k => ¬ p k)) F₂ := by
  have h := pushEntropy_reindex (Ω := Om Γ m) (splitE p) (Equiv.injective _).injOn
    (p' := productLaw (wtS Γ p) (wtS Γ (fun k => ¬ p k))) (fun q _ => wt_split p q) (fun z => F₂ z.2)
  rw [h, image_split]
  exact pushEntropy_productLaw_snd (wtS_nonneg _) (wtS_nonneg _) (wtS_sum hΓ _) (wtS_sum hΓ _) F₂

theorem pushWeight_split_fst (hΓ : Γ.Nonempty) (p : Fin m → Prop) [DecidablePred p] {α : Type*}
    [DecidableEq α] (F₁ : ({k // p k} → ℤ × ℤ) → α) (a : α) :
    pushWeight (Om Γ m) (wt Γ m) (fun q => F₁ (splitE p q).1) a = pushWeight (OmS Γ p) (wtS Γ p) F₁ a := by
  classical
  have hre := pushWeight_reindex (Ω := Om Γ m) (splitE p) (Equiv.injective _).injOn
    (p' := productLaw (wtS Γ p) (wtS Γ (fun k => ¬ p k))) (fun q _ => wt_split p q)
    (fun z : ({k // p k} → ℤ × ℤ) × ({k // ¬ p k} → ℤ × ℤ) => F₁ z.1) a
  rw [hre, image_split]
  have h := pushWeight_productLaw_pair (OmS Γ p) (OmS Γ (fun k => ¬ p k)) (wtS Γ p)
    (wtS Γ (fun k => ¬ p k)) F₁ (fun _ => ()) a ()
  have hu : pushWeight (OmS Γ (fun k => ¬ p k)) (wtS Γ (fun k => ¬ p k)) (fun _ => ()) () = 1 := by
    simpa [pushWeight] using wtS_sum hΓ (fun k => ¬ p k)
  rw [hu, mul_one] at h
  rw [← h]
  simp only [pushWeight]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext z; simp

end Split

/-! ## Forms supported on a group of copies -/

/-- The value of a form on a group of copies. -/
def fvalS (p : Fin m → Prop) [DecidablePred p] (f : Form m) (r : {k // p k} → ℤ × ℤ) : ℤ :=
  ∑ k : {k // p k}, ((f k).1 * (r k).1 + (f k).2 * (r k).2)

theorem fval_eq_fst {p : Fin m → Prop} [DecidablePred p] {f : Form m} (hf : ∀ k, ¬ p k → f k = (0, 0))
    (q : Fin m → ℤ × ℤ) : fval f q = fvalS p f (splitE p q).1 := by
  simp only [fval, fvalS, Equiv.piEquivPiSubtypeProd_apply]
  rw [← Fintype.sum_subtype_add_sum_subtype p]
  have h0 : ∑ k : {k : Fin m // ¬ p k}, ((f k).1 * (q k).1 + (f k).2 * (q k).2) = 0 :=
    Finset.sum_eq_zero fun k _ => by rw [hf k k.2]; ring
  rw [h0, add_zero]

theorem fval_eq_snd {p : Fin m → Prop} [DecidablePred p] {f : Form m} (hf : ∀ k, p k → f k = (0, 0))
    (q : Fin m → ℤ × ℤ) : fval f q = fvalS (fun k => ¬ p k) f (splitE p q).2 := by
  simp only [fval, fvalS, Equiv.piEquivPiSubtypeProd_apply]
  rw [← Fintype.sum_subtype_add_sum_subtype p]
  have h0 : ∑ k : {k : Fin m // p k}, ((f k).1 * (q k).1 + (f k).2 * (q k).2) = 0 :=
    Finset.sum_eq_zero fun k _ => by rw [hf k k.2]; ring
  rw [h0, zero_add]

/-- **Independence**: forms on disjoint groups of copies have additive joint entropy. -/
theorem HLm_indep {Γ : Finset (ℤ × ℤ)} (hΓ : Γ.Nonempty) (p : Fin m → Prop) [DecidablePred p]
    {l₁ l₂ : List (Form m)} (h₁ : ∀ f ∈ l₁, ∀ k, ¬ p k → f k = (0, 0))
    (h₂ : ∀ f ∈ l₂, ∀ k, p k → f k = (0, 0)) :
    HLm Γ m (l₁ ++ l₂) = HLm Γ m l₁ + HLm Γ m l₂ := by
  classical
  have e1 : ∀ q, l₁.map (fun c => fval c q) = l₁.map (fun c => fvalS p c (splitE p q).1) :=
    fun q => List.map_congr_left fun c hc => fval_eq_fst (h₁ c hc) q
  have e2 : ∀ q, l₂.map (fun c => fval c q) = l₂.map (fun c => fvalS (fun k => ¬ p k) c (splitE p q).2) :=
    fun q => List.map_congr_left fun c hc => fval_eq_snd (h₂ c hc) q
  rw [← HLm_pair]
  have hL : HLm Γ m l₁ = pushEntropy (OmS Γ p) (wtS Γ p) (fun r => l₁.map fun c => fvalS p c r) := by
    rw [← pushEntropy_split_fst hΓ p]
    unfold HLm
    simp only [e1]
  have hR : HLm Γ m l₂ = pushEntropy (OmS Γ (fun k => ¬ p k)) (wtS Γ (fun k => ¬ p k))
      (fun r => l₂.map fun c => fvalS (fun k => ¬ p k) c r) := by
    rw [← pushEntropy_split_snd hΓ p]
    unfold HLm
    simp only [e2]
  rw [hL, hR, ← pushEntropy_split hΓ p]
  simp only [e1, e2]

/-- Boolean support conditions, checked by `decide`. -/
def suppB (A : List (Fin m)) (f : Form m) : Bool :=
  (List.finRange m).all fun k => decide (k ∈ A) || ((f k).1 == 0 && (f k).2 == 0)

def offB (A : List (Fin m)) (f : Form m) : Bool :=
  A.all fun k => (f k).1 == 0 && (f k).2 == 0

theorem HLm_indepB {Γ : Finset (ℤ × ℤ)} (hΓ : Γ.Nonempty) (A : List (Fin m)) {l₁ l₂ : List (Form m)}
    (h₁ : l₁.all (suppB A) = true) (h₂ : l₂.all (offB A) = true) :
    HLm Γ m (l₁ ++ l₂) = HLm Γ m l₁ + HLm Γ m l₂ := by
  refine HLm_indep hΓ (fun k => k ∈ A) (fun f hf k hk => ?_) (fun f hf k hk => ?_)
  · have := List.all_eq_true.mp (List.all_eq_true.mp h₁ f hf) k (List.mem_finRange k)
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at this
    rcases this with h | ⟨h1, h2⟩
    · exact absurd h hk
    · exact Prod.ext h1 h2
  · have := List.all_eq_true.mp (List.all_eq_true.mp h₂ f hf) k hk
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact Prod.ext this.1 this.2

/-! ## The law of one copy -/

/-- A function of one copy `q k` has the law of that function under the uniform law on `Γ`. -/
theorem pushWeight_single {Γ : Finset (ℤ × ℤ)} (hΓ : Γ.Nonempty) (k : Fin m) {α : Type*} [DecidableEq α]
    (F : ℤ × ℤ → α) (a : α) :
    pushWeight (Om Γ m) (wt Γ m) (fun q => F (q k)) a = pushWeight Γ (fun _ => (#Γ : ℝ)⁻¹) F a := by
  classical
  have e1 : (fun q : Fin m → ℤ × ℤ => F (q k))
      = fun q => (fun r : {j // j = k} → ℤ × ℤ => F (r ⟨k, rfl⟩)) (splitE (fun j => j = k) q).1 := rfl
  rw [e1, pushWeight_split_fst hΓ (fun j => j = k) (fun r : {j // j = k} → ℤ × ℤ => F (r ⟨k, rfl⟩)) a]
  -- the group `{k}` is a copy of `Γ`
  have hinj : Set.InjOn (fun r : {j // j = k} → ℤ × ℤ => r ⟨k, rfl⟩) (OmS Γ (fun j => j = k) : Set _) := by
    intro r _ r' _ hrr
    funext j
    have : j = ⟨k, rfl⟩ := Subtype.ext j.2
    subst this
    exact hrr
  rw [pushWeight_reindex (fun r : {j // j = k} → ℤ × ℤ => r ⟨k, rfl⟩) hinj (p' := fun _ => (#Γ : ℝ)⁻¹)
    (fun r _ => by simp only [wtS, Fintype.card_subtype_eq, pow_one]) F a]
  have himg : (OmS Γ (fun j => j = k)).image (fun r : {j // j = k} → ℤ × ℤ => r ⟨k, rfl⟩) = Γ := by
    ext x
    simp only [Finset.mem_image, OmS, Fintype.mem_piFinset]
    constructor
    · rintro ⟨r, hr, rfl⟩; exact hr _
    · intro hx; exact ⟨fun _ => x, fun _ => hx, rfl⟩
  rw [himg]

/-- The form `x_k`. -/
def xF (k : Fin m) : Form m := fun j => if j = k then (1, 0) else (0, 0)

/-- The form `y_k`. -/
def yF (k : Fin m) : Form m := fun j => if j = k then (0, 1) else (0, 0)

theorem fval_xF (k : Fin m) (q : Fin m → ℤ × ℤ) : fval (xF k) q = (q k).1 := by
  simp only [fval, xF]
  rw [Finset.sum_eq_single k (fun j _ hj => by simp [hj]) (fun h => absurd (Finset.mem_univ k) h)]
  simp

theorem fval_yF (k : Fin m) (q : Fin m → ℤ × ℤ) : fval (yF k) q = (q k).2 := by
  simp only [fval, yF]
  rw [Finset.sum_eq_single k (fun j _ hj => by simp [hj]) (fun h => absurd (Finset.mem_univ k) h)]
  simp

/-- `H(x_k, y_k) = log #Γ`: one copy of the uniform law on `Γ`. -/
theorem HLm_pairK {Γ : Finset (ℤ × ℤ)} (hΓ : Γ.Nonempty) (k : Fin m) :
    HLm Γ m [xF k, yF k] = Real.log #Γ := by
  classical
  have e : (fun q : Fin m → ℤ × ℤ => [xF k, yF k].map fun c => fval c q)
      = fun q => (fun p : ℤ × ℤ => [p.1, p.2]) (q k) := by
    funext q; simp [fval_xF, fval_yF]
  unfold HLm
  rw [e]
  have hinj : Set.InjOn (fun p : ℤ × ℤ => [p.1, p.2]) (Γ : Set (ℤ × ℤ)) := by
    intro p _ p' _ h
    simp only [List.cons.injEq, and_true] at h
    exact Prod.ext h.1 h.2
  rw [show (#Γ : ℝ) = (#(Γ.image fun p : ℤ × ℤ => [p.1, p.2]) : ℝ) by
    rw [Finset.card_image_of_injOn hinj]]
  apply pushEntropy_eq_log_card_of_uniform (t := Γ.image fun p : ℤ × ℤ => [p.1, p.2])
  · ext y
    simp only [Finset.mem_image, Om, Fintype.mem_piFinset]
    constructor
    · rintro ⟨q, hq, rfl⟩; exact ⟨q k, hq k, rfl⟩
    · rintro ⟨p, hp, rfl⟩; exact ⟨fun _ => p, fun _ => hp, rfl⟩
  · intro y hy
    rw [Finset.card_image_of_injOn hinj, pushWeight_single hΓ k (fun p : ℤ × ℤ => [p.1, p.2])]
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
    simp only [pushWeight]
    have hfil : Γ.filter (fun x : ℤ × ℤ => [x.1, x.2] = [p.1, p.2]) = {p} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hx, hxe⟩; exact hinj hx hp hxe
      · rintro rfl; exact ⟨hp, rfl⟩
    rw [hfil, Finset.sum_singleton]

/-! ## Permuting the copies -/

/-- Transport of a form along a permutation of the copies (`(permF σ f) (σ k) = f k`). -/
def permF (σ : Equiv.Perm (Fin m)) (f : Form m) : Form m := fun k => f (σ.symm k)

theorem fval_permF (σ : Equiv.Perm (Fin m)) (f : Form m) (q : Fin m → ℤ × ℤ) :
    fval (permF σ f) q = fval f (fun k => q (σ k)) := by
  simp only [fval, permF]
  rw [← Equiv.sum_comp σ]
  simp only [Equiv.symm_apply_apply]

/-- **Exchangeability**: permuting the copies does not change a joint entropy. -/
theorem HLm_perm {Γ : Finset (ℤ × ℤ)} (σ : Equiv.Perm (Fin m)) (l : List (Form m)) :
    HLm Γ m (l.map (permF σ)) = HLm Γ m l := by
  classical
  unfold HLm
  have e : (fun q : Fin m → ℤ × ℤ => (l.map (permF σ)).map fun c => fval c q)
      = fun q => (fun q' : Fin m → ℤ × ℤ => l.map fun c => fval c q') (fun k => q (σ k)) := by
    funext q; simp [List.map_map, Function.comp_def, fval_permF]
  rw [e, pushEntropy_reindex (Ω := Om Γ m) (p := wt Γ m) (fun q : Fin m → ℤ × ℤ => fun k => q (σ k))
    (fun q _ q' _ h => by funext k; simpa using congrFun h (σ.symm k)) (p' := wt Γ m) (fun _ _ => rfl)
    (fun q' : Fin m → ℤ × ℤ => l.map fun c => fval c q')]
  have himg : (Om Γ m).image (fun q : Fin m → ℤ × ℤ => fun k => q (σ k)) = Om Γ m := by
    ext q
    simp only [Finset.mem_image, Om, Fintype.mem_piFinset]
    constructor
    · rintro ⟨q', hq', rfl⟩; exact fun k => hq' _
    · intro hq; exact ⟨fun k => q (σ.symm k), fun k => hq _, by funext k; simp⟩
  rw [himg]

end EntropyBounds.Iid
