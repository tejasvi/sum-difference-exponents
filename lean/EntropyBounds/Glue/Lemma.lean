import EntropyBounds.Glue.NonShannon
import EntropyBounds.Lemma.Basic

/-!
# Certificate lemmas applied to joint variables of a configuration

`C.lsp vs`: the letters `j ↦ (the values of the forms vs j)` on the sample space of a configuration, an `LSp` over
`List ℝ`.  `H_lsp`: the joint entropy of a set of letters is the entropy of the concatenated lists of forms
(`HS_jvN`, the bridge `HS_jvC` for any number of letters).  So a lemma proved for every family of letters
(`EntropyBounds/Lemma`) applies to any lists of forms of a valid configuration.
-/

open Finset

namespace EntropyBounds.Glue

open SumsDifferences SumsDifferences.CoupledEntropy SumsDifferences.NonShannon EntropyBounds.Iid EntropyBounds.Lem

variable {N : ℕ}

/-- The joint variables of a family of lists of forms. -/
noncomputable def jvN (C : Conf N) {k : ℕ} (vs : Fin k → List (Form N)) (j : Fin k) (i : C.ι) : List ℝ :=
  (vs j).map fun f => rval f (C.co i)

/-- The segment of a concatenation belonging to `j`. -/
def segN {k : ℕ} (vs : Fin k → List (Form N)) : List (Fin k) → Fin k → List ℝ → List ℝ
  | [], _, _ => []
  | j' :: Ls, j, y => if j = j' then y.take (vs j').length else segN vs Ls j (y.drop (vs j').length)

theorem segN_flatMap (C : Conf N) {k : ℕ} (vs : Fin k → List (Form N)) (i : C.ι) :
    ∀ (Ls : List (Fin k)), Ls.Nodup → ∀ j ∈ Ls,
      segN vs Ls j (Ls.flatMap fun t => jvN C vs t i) = jvN C vs j i := by
  intro Ls
  induction Ls with
  | nil => intro _ j hj; exact absurd hj List.not_mem_nil
  | cons j' Ls ih =>
    intro hnd j hj
    simp only [List.flatMap_cons, segN]
    by_cases h : j = j'
    · subst h
      rw [ite_eq_left rfl]
      exact List.take_left' (by simp [jvN])
    · rw [ite_eq_right h]
      have hj' : j ∈ Ls := by
        rcases List.mem_cons.mp hj with h' | h'
        · exact absurd h' h
        · exact h'
      rw [List.drop_left' (by simp [jvN])]
      exact ih (List.nodup_cons.mp hnd).2 j hj'

theorem flatMap_jvN (C : Conf N) {k : ℕ} (vs : Fin k → List (Form N)) (Ls : List (Fin k)) (i : C.ι) :
    (Ls.flatMap fun t => jvN C vs t i) = (Ls.flatMap vs).map fun f => rval f (C.co i) := by
  induction Ls with
  | nil => rfl
  | cons j Ls ih => rw [List.flatMap_cons, List.flatMap_cons, List.map_append, ih]; rfl

theorem HS_jvN (C : Conf N) (hp : ∀ i ∈ C.Ω, 0 ≤ C.p i) {k : ℕ} (vs : Fin k → List (Form N))
    (Ls : List (Fin k)) (hnd : Ls.Nodup) : HS C.Ω C.p (jvN C vs) Ls.toFinset = C.H (Ls.flatMap vs) := by
  classical
  rw [HS_eq]
  refine pushEntropy_eq_of_comp hp (fun t => Ls.flatMap t)
    (fun y => fun j => if j ∈ Ls.toFinset then segN vs Ls j y else 0) ?_ ?_
  · intro i _
    show Ls.flatMap (tup (jvN C vs) Ls.toFinset i) = (Ls.flatMap vs).map fun f => rval f (C.co i)
    rw [← flatMap_jvN]
    refine List.flatMap_congr fun j hj => ?_
    show (if j ∈ Ls.toFinset then jvN C vs j i else 0) = jvN C vs j i
    rw [ite_eq_left (List.mem_toFinset.mpr hj)]
  · intro i _
    funext j
    show (if j ∈ Ls.toFinset then segN vs Ls j ((Ls.flatMap vs).map fun f => rval f (C.co i)) else 0)
      = (if j ∈ Ls.toFinset then jvN C vs j i else 0)
    by_cases hj : j ∈ Ls
    · rw [ite_eq_left (List.mem_toFinset.mpr hj), ite_eq_left (List.mem_toFinset.mpr hj),
        ← flatMap_jvN, segN_flatMap C vs i Ls hnd j hj]
    · rw [ite_eq_right (fun h => hj (List.mem_toFinset.mp h)),
        ite_eq_right (fun h => hj (List.mem_toFinset.mp h))]

namespace Conf

/-- The letters `j ↦ vs j` on the sample space of `C`. -/
noncomputable abbrev lsp (C : Conf N) {k : ℕ} (vs : Fin k → List (Form N)) : LSp (List ℝ) k :=
  ⟨C.ι, C.Ω, C.p, jvN C vs⟩

theorem valid_lsp {C : Conf N} {Γ : Finset (ℝ × ℝ)} (hv : C.Valid Γ) {k : ℕ} (vs : Fin k → List (Form N)) :
    (C.lsp vs).Valid :=
  ⟨hv.nonneg, hv.sum_one⟩

theorem H_lsp {C : Conf N} (hp : ∀ i ∈ C.Ω, 0 ≤ C.p i) {k : ℕ} (vs : Fin k → List (Form N))
    (Ls : List (Fin k)) (hnd : Ls.Nodup) (S : Finset (Fin k)) (hS : Ls.toFinset = S) :
    (C.lsp vs).H S = C.H (Ls.flatMap vs) := by
  rw [← hS]
  exact HS_jvN C hp vs Ls hnd

end Conf

end EntropyBounds.Glue
