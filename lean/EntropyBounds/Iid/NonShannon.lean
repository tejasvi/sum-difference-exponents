import EntropyBounds.Iid.Basic
import SumDifference.CompanionInequality

/-!
# Non-Shannon instances on joint variables made of forms

Kleinwaks' `matus_ineq` and `companion_ineq` (Matúš' family and the Csirmaz–Csirmaz family, every `k`) are stated
for five random variables `v : Fin 5 → ι → G` through the subset entropy `HS`.  Here the five variables are
lists of forms (`jv vs j q = the values of the forms vs j at q`, valued in `List ℤ`), and

  `HS (Om Γ m) (wt Γ m) (jv vs) Ls.toFinset = HLm Γ m (Ls.flatMap vs)`     (`HS_jv`, `Ls` without repetition),

so each subset entropy of an instance is the joint entropy of the concatenated lists.
-/

namespace EntropyBounds.Iid

open SumsDifferences SumsDifferences.NonShannon

variable {m : ℕ}

/-- Padding value for `HS` on `List ℤ`-valued variables. -/
scoped instance instZeroListInt : Zero (List ℤ) := ⟨[]⟩

/-- The five joint variables of a non-Shannon instance. -/
def jv (vs : Fin 5 → List (Form m)) (j : Fin 5) (q : Fin m → ℤ × ℤ) : List ℤ := (vs j).map fun f => fval f q

/-- The segment of a concatenation belonging to `j`. -/
def seg (vs : Fin 5 → List (Form m)) : List (Fin 5) → Fin 5 → List ℤ → List ℤ
  | [], _, _ => []
  | j' :: Ls, j, y => if j = j' then y.take (vs j').length else seg vs Ls j (y.drop (vs j').length)

theorem seg_flatMap (vs : Fin 5 → List (Form m)) (q : Fin m → ℤ × ℤ) :
    ∀ (Ls : List (Fin 5)), Ls.Nodup → ∀ j ∈ Ls,
      seg vs Ls j (Ls.flatMap fun i => jv vs i q) = jv vs j q := by
  intro Ls
  induction Ls with
  | nil => intro _ j hj; exact absurd hj List.not_mem_nil
  | cons j' Ls ih =>
    intro hnd j hj
    simp only [List.flatMap_cons, seg]
    by_cases h : j = j'
    · subst h
      rw [ite_eq_left rfl]
      exact List.take_left' (by simp [jv])
    · rw [ite_eq_right h]
      have hj' : j ∈ Ls := by
        rcases List.mem_cons.mp hj with h' | h'
        · exact absurd h' h
        · exact h'
      rw [List.drop_left' (by simp [jv])]
      exact ih (List.nodup_cons.mp hnd).2 j hj'

theorem flatMap_jv (vs : Fin 5 → List (Form m)) (Ls : List (Fin 5)) (q : Fin m → ℤ × ℤ) :
    (Ls.flatMap fun i => jv vs i q) = (Ls.flatMap vs).map fun f => fval f q := by
  induction Ls with
  | nil => rfl
  | cons j Ls ih => rw [List.flatMap_cons, List.flatMap_cons, List.map_append, ih]; rfl

/-- **Bridge**: subset entropies of a five-variable instance are joint entropies of concatenations. -/
theorem HS_jv (Γ : Finset (ℤ × ℤ)) (vs : Fin 5 → List (Form m)) (Ls : List (Fin 5)) (hnd : Ls.Nodup) :
    HS (Om Γ m) (wt Γ m) (jv vs) Ls.toFinset = HLm Γ m (Ls.flatMap vs) := by
  classical
  rw [HS_eq]
  refine pushEntropy_eq_of_comp (wt_nonneg Γ m) (fun t => Ls.flatMap t)
    (fun y => fun j => if j ∈ Ls.toFinset then seg vs Ls j y else 0) ?_ ?_
  · intro q _
    show Ls.flatMap (tup (jv vs) Ls.toFinset q) = (Ls.flatMap vs).map fun f => fval f q
    rw [← flatMap_jv]
    refine List.flatMap_congr fun j hj => ?_
    show (if j ∈ Ls.toFinset then jv vs j q else 0) = jv vs j q
    rw [ite_eq_left (List.mem_toFinset.mpr hj)]
  · intro q _
    funext j
    show (if j ∈ Ls.toFinset then seg vs Ls j ((Ls.flatMap vs).map fun f => fval f q) else 0)
      = (if j ∈ Ls.toFinset then jv vs j q else 0)
    by_cases hj : j ∈ Ls
    · rw [ite_eq_left (List.mem_toFinset.mpr hj), ite_eq_left (List.mem_toFinset.mpr hj),
        ← flatMap_jv, seg_flatMap vs q Ls hnd j hj]
    · rw [ite_eq_right (fun h => hj (List.mem_toFinset.mp h)),
        ite_eq_right (fun h => hj (List.mem_toFinset.mp h))]

end EntropyBounds.Iid
