import EntropyBounds.GlueG.Copy
import SumDifference.CompanionInequality

/-!
# Non-Shannon instances, determination chains, and the base configuration (values in `G`)

* `HS_jvC`: for five joint variables made of lists of forms (`jvC C vs j i = the values of the forms vs j at i`),
  the subset entropies of Kleinwaks' `HS` are joint entropies of concatenations,
  `HS C.Ω C.p (jvC C vs) Ls.toFinset = C.H (Ls.flatMap vs)` (`Ls` without repetition), so `matus_ineq` applies to
  any five lists of forms of a valid configuration.
* `Conf.Det.trans`, `Conf.det_of_chain`: determinations compose (closure rounds).
* `Conf.H_base_*`: the base configuration's entropies of `(x₀, y₀)`, `x₀`, `y₀`, `x₀ + y₀` are those of the law
  `p` on `Γ` and of its images.
-/

open Finset

namespace EntropyBounds.GlueG

open SumsDifferences SumsDifferences.CoupledEntropy SumsDifferences.NonShannon EntropyBounds.Iid

variable {N : ℕ} {G : Type} [AddCommGroup G]

/-- Padding value for `HS` on `List G`-valued variables. -/
scoped instance instZeroListG {G : Type} : Zero (List G) := ⟨[]⟩

/-- The five joint variables of a non-Shannon instance. -/
noncomputable def jvC (C : Conf N G) (vs : Fin 5 → List (Form N)) (j : Fin 5) (i : C.ι) : List G :=
  (vs j).map fun f => rval f (C.co i)

/-- The segment of a concatenation belonging to `j`. -/
def segC (vs : Fin 5 → List (Form N)) : List (Fin 5) → Fin 5 → List G → List G
  | [], _, _ => []
  | j' :: Ls, j, y => if j = j' then y.take (vs j').length else segC vs Ls j (y.drop (vs j').length)

theorem segC_flatMap (C : Conf N G) (vs : Fin 5 → List (Form N)) (i : C.ι) :
    ∀ (Ls : List (Fin 5)), Ls.Nodup → ∀ j ∈ Ls,
      segC vs Ls j (Ls.flatMap fun k => jvC C vs k i) = jvC C vs j i := by
  intro Ls
  induction Ls with
  | nil => intro _ j hj; exact absurd hj List.not_mem_nil
  | cons j' Ls ih =>
    intro hnd j hj
    simp only [List.flatMap_cons, segC]
    by_cases h : j = j'
    · subst h
      rw [ite_eq_left rfl]
      exact List.take_left' (by simp [jvC])
    · rw [ite_eq_right h]
      have hj' : j ∈ Ls := by
        rcases List.mem_cons.mp hj with h' | h'
        · exact absurd h' h
        · exact h'
      rw [List.drop_left' (by simp [jvC])]
      exact ih (List.nodup_cons.mp hnd).2 j hj'

theorem flatMap_jvC (C : Conf N G) (vs : Fin 5 → List (Form N)) (Ls : List (Fin 5)) (i : C.ι) :
    (Ls.flatMap fun k => jvC C vs k i) = (Ls.flatMap vs).map fun f => rval f (C.co i) := by
  induction Ls with
  | nil => rfl
  | cons j Ls ih => rw [List.flatMap_cons, List.flatMap_cons, List.map_append, ih]; rfl

variable [DecidableEq G]

/-- **Bridge**: subset entropies of a five-variable instance are joint entropies of concatenations. -/
theorem HS_jvC (C : Conf N G) (hp : ∀ i ∈ C.Ω, 0 ≤ C.p i) (vs : Fin 5 → List (Form N)) (Ls : List (Fin 5))
    (hnd : Ls.Nodup) : HS C.Ω C.p (jvC C vs) Ls.toFinset = C.H (Ls.flatMap vs) := by
  classical
  rw [HS_eq]
  refine pushEntropy_eq_of_comp hp (fun t => Ls.flatMap t)
    (fun y => fun j => if j ∈ Ls.toFinset then segC vs Ls j y else 0) ?_ ?_
  · intro i _
    show Ls.flatMap (tup (jvC C vs) Ls.toFinset i) = (Ls.flatMap vs).map fun f => rval f (C.co i)
    rw [← flatMap_jvC]
    refine List.flatMap_congr fun j hj => ?_
    show (if j ∈ Ls.toFinset then jvC C vs j i else 0) = jvC C vs j i
    rw [ite_eq_left (List.mem_toFinset.mpr hj)]
  · intro i _
    funext j
    show (if j ∈ Ls.toFinset then segC vs Ls j ((Ls.flatMap vs).map fun f => rval f (C.co i)) else 0)
      = (if j ∈ Ls.toFinset then jvC C vs j i else 0)
    by_cases hj : j ∈ Ls
    · rw [ite_eq_left (List.mem_toFinset.mpr hj), ite_eq_left (List.mem_toFinset.mpr hj),
        ← flatMap_jvC, segC_flatMap C vs i Ls hnd j hj]
    · rw [ite_eq_right (fun h => hj (List.mem_toFinset.mp h)),
        ite_eq_right (fun h => hj (List.mem_toFinset.mp h))]

namespace Conf

variable {C : Conf N G}

/-- Determinations compose. -/
theorem Det.trans {l l' : List (Form N)} {f : Form N} (h : ∀ g ∈ l', C.Det l g) (h' : C.Det l' f) :
    C.Det l f := by
  classical
  obtain ⟨φ, hφ⟩ := h'
  refine ⟨fun y => φ (l'.map fun g => if hg : C.Det l g then hg.choose y else 0), fun i hi => ?_⟩
  rw [← hφ i hi]
  show φ _ = φ _
  congr 1
  refine List.map_congr_left fun g hg => ?_
  rw [dite_eq_left (h g hg)]
  exact (h g hg).choose_spec i hi

/-- A list determines its own members. -/
theorem Det.of_mem {l : List (Form N)} {f : Form N} (hf : f ∈ l) : C.Det l f := by
  classical
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hf
  exact ⟨fun y => y.getD k 0, fun i _ => by simp [hk]⟩

end Conf

/-! ## The base configuration -/

theorem rval_xF_const (k : Fin N) (q : G × G) : rval (xF k) (fun _ => q) = q.1 := by
  simp only [rval, xF]
  rw [Finset.sum_eq_single k (fun j _ hj => by simp [hj]) (fun h => absurd (Finset.mem_univ k) h)]
  simp

theorem rval_yF_const (k : Fin N) (q : G × G) : rval (yF k) (fun _ => q) = q.2 := by
  simp only [rval, yF]
  rw [Finset.sum_eq_single k (fun j _ hj => by simp [hj]) (fun h => absurd (Finset.mem_univ k) h)]
  simp

theorem H_base_list {Γ : Finset (G × G)} {p : G × G → ℝ} (l : List (Form N)) :
    (base (N := N) Γ p).H l = pushEntropy Γ p (fun q => l.map fun f => rval f (fun _ => q)) := rfl

theorem H_base_pair {Γ : Finset (G × G)} {p : G × G → ℝ} (hp : ∀ q ∈ Γ, 0 ≤ p q) (k : Fin N) :
    (base (N := N) Γ p).H [xF k, yF k] = pushEntropy Γ p id := by
  rw [H_base_list]
  refine pushEntropy_eq_of_comp hp (fun y => (y.getD 0 0, y.getD 1 0)) (fun z => [z.1, z.2]) ?_ ?_
  · intro q _; simp [rval_xF_const, rval_yF_const]
  · intro q _; simp [rval_xF_const, rval_yF_const]

theorem H_base_single {Γ : Finset (G × G)} {p : G × G → ℝ} (hp : ∀ q ∈ Γ, 0 ≤ p q) (f : Form N)
    (g : G × G → G) (hg : ∀ q, rval f (fun _ => q) = g q) :
    (base (N := N) Γ p).H [f] = pushEntropy Γ p g := by
  rw [H_base_list]
  refine pushEntropy_eq_of_comp hp (fun y => y.getD 0 0) (fun z => [z]) ?_ ?_
  · intro q _; simp [hg]
  · intro q _; simp [hg]

/-- The standing hypotheses: doubling is injective on `G`, distinct differences on the support `Γ`, a probability
weight. -/
structure Hyp (Γ : Finset (G × G)) (p : G × G → ℝ) : Prop where
  two : ∀ x : G, x + x = 0 → x = 0
  inj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q'
  nonneg : ∀ q ∈ Γ, 0 ≤ p q
  sum_one : ∑ q ∈ Γ, p q = 1

theorem H_base_pairB {Γ : Finset (G × G)} {p : G × G → ℝ} (hp : ∀ q ∈ Γ, 0 ≤ p q) (f g : Form N) (k : Fin N)
    (hf : eqF f (xF k) = true) (hg : eqF g (yF k) = true) :
    (base (N := N) Γ p).H [f, g] = pushEntropy Γ p (fun q => q) := by
  rw [eqF_iff.mp hf, eqF_iff.mp hg]
  exact H_base_pair hp k

theorem H_base_xB {Γ : Finset (G × G)} {p : G × G → ℝ} (hp : ∀ q ∈ Γ, 0 ≤ p q) (f : Form N) (k : Fin N)
    (hf : eqF f (xF k) = true) : (base (N := N) Γ p).H [f] = pushEntropy Γ p (fun q => q.1) := by
  rw [eqF_iff.mp hf]
  exact H_base_single hp _ _ fun q => rval_xF_const k q

theorem H_base_yB {Γ : Finset (G × G)} {p : G × G → ℝ} (hp : ∀ q ∈ Γ, 0 ≤ p q) (f : Form N) (k : Fin N)
    (hf : eqF f (yF k) = true) : (base (N := N) Γ p).H [f] = pushEntropy Γ p (fun q => q.2) := by
  rw [eqF_iff.mp hf]
  exact H_base_single hp _ _ fun q => rval_yF_const k q

theorem H_base_sumB {Γ : Finset (G × G)} {p : G × G → ℝ} (hp : ∀ q ∈ Γ, 0 ≤ p q) (f : Form N) (k : Fin N)
    (hf : eqF f (addF (xF k) (yF k)) = true) :
    (base (N := N) Γ p).H [f] = pushEntropy Γ p (fun q => q.1 + q.2) := by
  rw [eqF_iff.mp hf]
  exact H_base_single hp _ _ fun q => by rw [rval_addF, rval_xF_const, rval_yF_const]

end EntropyBounds.GlueG
