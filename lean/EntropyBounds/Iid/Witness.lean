import EntropyBounds.Iid.Indep

/-!
# Checkable witnesses for identities between joint entropies

* `DW m`: a determination witness for one form `f` from a list `l`: `c • f = Σ msᵢ lᵢ + g`, `c ≠ 0`, with
  `Σ (wit k)ᵢ lᵢ = x_k − y_k` for every copy `k` that `g` uses.  `checkDWs l₁ l₂ ws` checks a witness for every
  form of `l₂`; `HLm_eq_wit` turns witnesses in both directions into `HLm Γ m l₁ = HLm Γ m l₂`.
* `mkPerm`: a permutation of the copies from its two tables; `HLm_permB`: exchangeability with a Boolean check that
  the transported list is the given one.

All checks are Boolean functions on integer data, closed by `decide`; the generated certificate modules supply the
witnesses (found by the exporter by exact rational linear algebra).
-/

open Finset

namespace EntropyBounds.Iid

open SumsDifferences SumsDifferences.CoupledEntropy SumsDifferences.CoupledForms

variable {m : ℕ}

/-- A determination witness. -/
structure DW (m : ℕ) where
  c : ℤ
  ms : List ℤ
  g : Form m
  wc : Fin m → ℤ
  wit : Fin m → List ℤ

/-- Check one witness for `f` from `l`. -/
def checkDW (l : List (Form m)) (f : Form m) (w : DW m) : Bool :=
  w.c != 0 && eqF (smulF w.c f) (addF (lcF w.ms l) w.g) &&
    (List.finRange m).all (fun k => ((w.g k).1 == 0 && (w.g k).2 == 0) ||
      (w.wc k != 0 && eqF (lcF (w.wit k) l) (smulF (w.wc k) (dform k))))

/-- Check witnesses for every form of `l₂` from `l₁`. -/
def checkDWs (l₁ l₂ : List (Form m)) (ws : List (DW m)) : Bool :=
  ws.length == l₂.length && (l₂.zip ws).all (fun p => checkDW l₁ p.1 p.2)

theorem det_of_checkDW {Γ : Finset (ℤ × ℤ)} (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q')
    {l : List (Form m)} {f : Form m} {w : DW m} (h : checkDW l f w = true) : Det Γ l f := by
  simp only [checkDW, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨hc, hf⟩, hg⟩ := h
  exact Det.gen hinj w.c hc w.ms w.g w.wc w.wit hf hg

theorem det_of_checkDWs {Γ : Finset (ℤ × ℤ)} (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q')
    {l₁ l₂ : List (Form m)} {ws : List (DW m)} (h : checkDWs l₁ l₂ ws = true) : ∀ f ∈ l₂, Det Γ l₁ f := by
  simp only [checkDWs, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hlen, hall⟩ := h
  intro f hf
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hf
  have hi' : i < ws.length := hlen ▸ hi
  have hmem : (l₂[i], ws[i]) ∈ l₂.zip ws := by
    rw [List.mem_iff_getElem]
    exact ⟨i, by simp [hi, hi'], by simp⟩
  exact det_of_checkDW hinj (List.all_eq_true.mp hall _ hmem)

/-- **Identity from witnesses**: `HLm Γ m l₁ = HLm Γ m l₂`. -/
theorem HLm_eq_wit {Γ : Finset (ℤ × ℤ)} (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q')
    (l₁ l₂ : List (Form m)) (w₁₂ w₂₁ : List (DW m))
    (h₁₂ : checkDWs l₁ l₂ w₁₂ = true) (h₂₁ : checkDWs l₂ l₁ w₂₁ = true) :
    HLm Γ m l₁ = HLm Γ m l₂ :=
  HLm_eq_of_det (det_of_checkDWs hinj h₁₂) (det_of_checkDWs hinj h₂₁)

/-- A determination of the empty list: `HLm Γ m l = 0` when every form of `l` is determined by `[]`
(i.e. is the zero form). -/
theorem HLm_eq_zero_wit {Γ : Finset (ℤ × ℤ)} (hΓ : Γ.Nonempty)
    (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q')
    (l : List (Form m)) (w : List (DW m)) (h : checkDWs [] l w = true) : HLm Γ m l = 0 := by
  rw [← HLm_nil (m := m) hΓ]
  exact HLm_eq_of_det (fun f hf => absurd hf List.not_mem_nil) (det_of_checkDWs hinj h)

/-! ## Permutations given by tables -/

/-- Boolean equality of lists of forms. -/
def listEqF : List (Form m) → List (Form m) → Bool
  | [], [] => true
  | f :: l, g :: l' => eqF f g && listEqF l l'
  | _, _ => false

theorem listEqF_iff {l l' : List (Form m)} : listEqF l l' = true → l = l' := by
  induction l generalizing l' with
  | nil => cases l' <;> simp [listEqF]
  | cons f l ih =>
    cases l' with
    | nil => simp [listEqF]
    | cons g l' =>
      simp only [listEqF, Bool.and_eq_true]
      rintro ⟨h1, h2⟩
      rw [eqF_iff.mp h1, ih h2]

/-- Two tables that are mutually inverse (checked by `decide`). -/
def permOK (fw bw : Fin m → Fin m) : Bool :=
  (List.finRange m).all fun k => bw (fw k) == k && fw (bw k) == k

/-- The permutation of the copies with table `fw` (and inverse table `bw`). -/
def mkPerm (fw bw : Fin m → Fin m) (h : permOK fw bw = true) : Equiv.Perm (Fin m) where
  toFun := fw
  invFun := bw
  left_inv := fun k => by
    have := List.all_eq_true.mp h k (List.mem_finRange k)
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact this.1
  right_inv := fun k => by
    have := List.all_eq_true.mp h k (List.mem_finRange k)
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact this.2

/-- Transport of a form along the permutation with tables `fw`, `bw` (computable). -/
def permT (bw : Fin m → Fin m) (f : Form m) : Form m := fun k => f (bw k)

theorem permF_mkPerm (fw bw : Fin m → Fin m) (h : permOK fw bw = true) (f : Form m) :
    permF (mkPerm fw bw h) f = permT bw f := rfl

/-- **Exchangeability with a table check.** -/
theorem HLm_permB {Γ : Finset (ℤ × ℤ)} (fw bw : Fin m → Fin m) (h : permOK fw bw = true)
    (G τG : List (Form m)) (hτ : listEqF (G.map (permT bw)) τG = true) :
    HLm Γ m τG = HLm Γ m G := by
  rw [← listEqF_iff hτ]
  have e : G.map (permT bw) = G.map (permF (mkPerm fw bw h)) := rfl
  rw [e]
  exact HLm_perm _ G

/-- `H(x_k, y_k) = log #Γ` for a list checked to be `[x_k, y_k]`. -/
theorem HLm_pairKB {Γ : Finset (ℤ × ℤ)} (hΓ : Γ.Nonempty) (k : Fin m) (l : List (Form m))
    (h : listEqF l [xF k, yF k] = true) : HLm Γ m l = Real.log #Γ := by
  rw [listEqF_iff h]
  exact HLm_pairK hΓ k

end EntropyBounds.Iid
