import EntropyBounds.TwoSet.Common

/-!
# Both copies on one probability space

`mirror Γ = {(−y, −x) : (x, y) ∈ Γ}`.  The coordinatewise map `mirQ q = (k ↦ (−(q k).2, −(q k).1))` carries `Γ^m`
bijectively onto `(mirror Γ)^m` with the same uniform weight, and `fval f (mirQ q) = fval (mirF f) q` with
`mirF f k = (−(f k).2, −(f k).1)`.  Hence

  `HLm (mirror Γ) m l = HLm Γ m (l.map mirF)`                                         (`HLm_mirror`):

the reflected copy's vertices are realised as `(−Y_k, −X_k)` of the unreflected copy's vertices (the `rshare` rows of
the certificates; a reflected `W` vertex is moved to a `W` vertex of transposed law by a permutation of the copies,
`HLm_permB`).
-/

open Finset

namespace EntropyBounds.TwoSet

open SumsDifferences SumsDifferences.CoupledEntropy SumsDifferences.CoupledForms EntropyBounds.Iid

variable {m : ℕ}

/-- The reflection on forms: `x_k ↦ −y_k`, `y_k ↦ −x_k` (computable). -/
def mirF (f : Form m) : Form m := fun k => (-(f k).2, -(f k).1)

/-- The reflection on points of `Γ^m`. -/
def mirQ (q : Fin m → ℤ × ℤ) : Fin m → ℤ × ℤ := fun k => (-(q k).2, -(q k).1)

theorem fval_mirF (f : Form m) (q : Fin m → ℤ × ℤ) : fval (mirF f) q = fval f (mirQ q) := by
  simp only [fval, mirF, mirQ]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem mirQ_mirQ (q : Fin m → ℤ × ℤ) : mirQ (mirQ q) = q := by
  funext k
  simp [mirQ]

theorem image_mirQ (Γ : Finset (ℤ × ℤ)) : (Om Γ m).image mirQ = Om (mirror Γ) m := by
  ext q
  simp only [Finset.mem_image, mem_Om, mirror]
  constructor
  · rintro ⟨q', hq', rfl⟩ k
    exact ⟨q' k, hq' k, rfl⟩
  · intro hq
    refine ⟨mirQ q, fun k => ?_, mirQ_mirQ q⟩
    obtain ⟨a, ha, hak⟩ := hq k
    have e : mirQ q k = a := by
      simp only [mirQ, ← hak, neg_neg]
    rw [e]
    exact ha

/-- **The reflected copy on the unreflected copy's space.** -/
theorem HLm_mirror (Γ : Finset (ℤ × ℤ)) (l : List (Form m)) :
    HLm (mirror Γ) m l = HLm Γ m (l.map mirF) := by
  classical
  unfold HLm
  have e : (fun q : Fin m → ℤ × ℤ => (l.map mirF).map fun c => fval c q)
      = fun q => (fun q' : Fin m → ℤ × ℤ => l.map fun c => fval c q') (mirQ q) := by
    funext q
    simp [List.map_map, Function.comp_def, fval_mirF]
  rw [e, pushEntropy_reindex (Ω := Om Γ m) (p := wt Γ m) mirQ
    (fun q _ q' _ h => by rw [← mirQ_mirQ q, h, mirQ_mirQ]) (p' := wt (mirror Γ) m)
    (fun _ _ => by simp [wt, card_mirror]) (fun q' : Fin m → ℤ × ℤ => l.map fun c => fval c q'), image_mirQ]

/-- `HLm (mirror Γ) m l₁ = HLm Γ m l₂` from a check that `l₂` is the reflection of `l₁` followed by the permutation of
the copies with tables `fw`, `bw`. -/
theorem HLm_mirror_permB (Γ : Finset (ℤ × ℤ)) (fw bw : Fin m → Fin m) (h : permOK fw bw = true)
    (l₁ l₂ : List (Form m)) (hτ : listEqF ((l₁.map mirF).map (permT bw)) l₂ = true) :
    HLm (mirror Γ) m l₁ = HLm Γ m l₂ := by
  rw [HLm_mirror, HLm_permB fw bw h _ _ hτ]

end EntropyBounds.TwoSet
