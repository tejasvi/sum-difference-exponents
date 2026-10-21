import EntropyBounds.Glue.Basic
import SumDifference.CopyLemma

/-!
# Copy steps

`C.copy src V` adds copies of vertices: a vertex `v` with `src v = some u` becomes a copy of `u`, and the copies
are conditionally independent of the whole configuration given the forms `V` (Kleinwaks' `copySet` / `copyW`,
the Zhang–Yeung copy over the key `C.key V`).  Vertices with `src v = none` keep their values.  The points of the
new sample space are pairs `(i, j)` of old points with the same key; the copies are read off `j`.

* `valid_copy`: the copy of a valid configuration is valid.
* `H_copy_old`, `rel_copy_old`: lists of forms that do not use the new vertices keep their entropy, and old
  relations stay relations.
* `rval_mix_new`: a form `b` on the new vertices takes the value of its pull-back `pullF src b` at `j`.
* `H_copy_eqlaw`: `H(B, V') = H(A, V')` for `B` on the new vertices with pull-back `A`, and `V' ⊆ V`
  (`(copies, V)` has the law of `(sources, V)`).
* `H_copy_ci`: `H(old, B, V) + H(V) = H(old, V) + H(B, V)` (conditional independence given `V`).
* `rel_copy_new`: if `V` determines the old form `α` and `b` is a form on the new vertices with pull-back `α`,
  then `b − α` is a relation of the new configuration.
-/

open Finset

namespace EntropyBounds.Glue

open SumsDifferences SumsDifferences.CoupledEntropy SumsDifferences.NonShannon EntropyBounds.Iid

variable {N : ℕ}

/-- Mixing two points: vertex `v` is vertex `u` of the second point when `src v = some u`. -/
def mix (src : Fin N → Option (Fin N)) (q q' : Fin N → ℝ × ℝ) : Fin N → ℝ × ℝ :=
  fun v => match src v with
    | some u => q' u
    | none => q v

/-- `f` does not use the new vertices. -/
def oldF (src : Fin N → Option (Fin N)) (f : Form N) : Bool :=
  (List.finRange N).all fun v => (src v).isNone || ((f v).1 == 0 && (f v).2 == 0)

/-- `b` only uses the new vertices. -/
def newF (src : Fin N → Option (Fin N)) (b : Form N) : Bool :=
  (List.finRange N).all fun v => (src v).isSome || ((b v).1 == 0 && (b v).2 == 0)

/-- The pull-back of a form on the new vertices to their sources. -/
def pullF (src : Fin N → Option (Fin N)) (b : Form N) : Form N :=
  fun u => ((List.finRange N).map fun v => if src v = some u then b v else (0, 0)).sum

theorem rval_mix_old {src : Fin N → Option (Fin N)} {f : Form N} (h : oldF src f = true)
    (q q' : Fin N → ℝ × ℝ) : rval f (mix src q q') = rval f q := by
  unfold rval
  refine Finset.sum_congr rfl fun v _ => ?_
  have hv := List.all_eq_true.mp h v (List.mem_finRange v)
  simp only [Bool.or_eq_true, Option.isNone_iff_eq_none, Bool.and_eq_true, beq_iff_eq] at hv
  rcases hv with hn | ⟨h1, h2⟩
  · simp only [mix, hn]
  · rw [h1, h2]; simp

theorem pullF_apply (src : Fin N → Option (Fin N)) (b : Form N) (u : Fin N) :
    pullF src b u = ∑ v, if src v = some u then b v else (0, 0) := by
  rw [pullF, Fin.sum_univ_def]

theorem rval_mix_new {src : Fin N → Option (Fin N)} {b : Form N} (h : newF src b = true)
    (q q' : Fin N → ℝ × ℝ) : rval b (mix src q q') = rval (pullF src b) q' := by
  have hterm : ∀ v, (((b v).1 : ℝ) * (mix src q q' v).1 + ((b v).2 : ℝ) * (mix src q q' v).2)
      = ∑ u, if src v = some u then (((b v).1 : ℝ) * (q' u).1 + ((b v).2 : ℝ) * (q' u).2) else 0 := by
    intro v
    have hv := List.all_eq_true.mp h v (List.mem_finRange v)
    simp only [Bool.or_eq_true, Option.isSome_iff_exists, Bool.and_eq_true, beq_iff_eq] at hv
    rcases hs : src v with _ | u
    · have : (b v).1 = 0 ∧ (b v).2 = 0 := by
        rcases hv with ⟨u, hu⟩ | h12
        · rw [hs] at hu; exact absurd hu (by simp)
        · exact h12
      rw [this.1, this.2]; simp
    · rw [Finset.sum_eq_single u (fun w _ hw => by simp [hw.symm]) (fun hu => absurd (Finset.mem_univ u) hu)]
      simp [mix, hs]
  unfold rval
  rw [Finset.sum_congr rfl fun v _ => hterm v, Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [pullF_apply, Prod.fst_sum, Prod.snd_sum]
  push_cast
  rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  split_ifs <;> simp

namespace Conf

/-- The key of a copy step: the values of the forms `V`. -/
noncomputable abbrev key (C : Conf N) (V : List (Form N)) (i : C.ι) : List ℝ := V.map fun f => rval f (C.co i)

/-- **The copy step.** -/
noncomputable abbrev copy (C : Conf N) (src : Fin N → Option (Fin N)) (V : List (Form N)) : Conf N where
  ι := C.ι × C.ι
  Ω := copySet C.Ω (C.key V)
  p := copyW C.Ω C.p (C.key V)
  co := fun ij => mix src (C.co ij.1) (C.co ij.2)

variable {C : Conf N} {Γ : Finset (ℝ × ℝ)} {src : Fin N → Option (Fin N)} {V : List (Form N)}

theorem valid_copy (hv : C.Valid Γ) (src : Fin N → Option (Fin N)) (V : List (Form N)) :
    (C.copy src V).Valid Γ where
  nonneg := fun q hq => copyW_nonneg hv.nonneg _ hq
  sum_one := by
    have := copy_sum_fst hv.nonneg (C.key V) (fun _ => (1 : ℝ))
    simp only [mul_one] at this
    show ∑ q ∈ copySet C.Ω (C.key V), copyW C.Ω C.p (C.key V) q = 1
    rw [this, hv.sum_one]
  mem := by
    intro q hq v
    have hq' := mem_copySet.mp hq
    show mix src (C.co q.1) (C.co q.2) v ∈ Γ
    unfold mix
    split
    · exact hv.mem _ hq'.2.1 _
    · exact hv.mem _ hq'.1 _

theorem H_copy_old (hv : C.Valid Γ) (l : List (Form N)) (hl : l.all (oldF src) = true) :
    (C.copy src V).H l = C.H l := by
  have e : ∀ q ∈ copySet C.Ω (C.key V), (l.map fun f => rval f (mix src (C.co q.1) (C.co q.2)))
      = (fun i => l.map fun f => rval f (C.co i)) q.1 := by
    intro q _
    refine List.map_congr_left fun f hf => ?_
    exact rval_mix_old (List.all_eq_true.mp hl f hf) _ _
  show pushEntropy (copySet C.Ω (C.key V)) (copyW C.Ω C.p (C.key V))
    (fun q => l.map fun f => rval f (mix src (C.co q.1) (C.co q.2)))
      = pushEntropy C.Ω C.p (fun i => l.map fun f => rval f (C.co i))
  exact (pushEntropy_congr e).trans
    (pushEntropy_copy_fst hv.nonneg (C.key V) (fun i => l.map fun f => rval f (C.co i)))

theorem rel_copy_old {r : Form N} (hr : C.Rel r) (h : oldF src r = true) : (C.copy src V).Rel r := by
  intro q hq
  show rval r (mix src (C.co q.1) (C.co q.2)) = 0
  rw [rval_mix_old h]
  exact hr _ (mem_copySet.mp hq).1

/-- On the copy set, the forms of `V` agree at the two points. -/
theorem key_eq_of_mem {q : C.ι × C.ι} (hq : q ∈ copySet C.Ω (C.key V)) {f : Form N} (hf : f ∈ V) :
    rval f (C.co q.1) = rval f (C.co q.2) := by
  have h := (mem_copySet.mp hq).2.2
  unfold key at h
  exact List.map_inj_left.mp h f hf

/-- **Equal law of copies and sources.** -/
theorem H_copy_eqlaw (hv : C.Valid Γ) (hVold : V.all (oldF src) = true) (B LV A : List (Form N))
    (hB : B.all (newF src) = true) (hA : listEqF (B.map (pullF src)) A = true)
    (hAold : A.all (oldF src) = true) (hLV : LV.all (fun f => V.any (eqF f)) = true) :
    (C.copy src V).H (B ++ LV) = (C.copy src V).H (A ++ LV) := by
  have hLVold : (A ++ LV).all (oldF src) = true := by
    rw [List.all_append, hAold, Bool.true_and]
    refine List.all_eq_true.mpr fun f hf => ?_
    obtain ⟨g, hg, hfg⟩ := List.any_eq_true.mp (List.all_eq_true.mp hLV f hf)
    rw [eqF_iff.mp hfg]
    exact List.all_eq_true.mp hVold g hg
  rw [H_copy_old hv _ hLVold]
  have e : ∀ q ∈ copySet C.Ω (C.key V), ((B ++ LV).map fun f => rval f (mix src (C.co q.1) (C.co q.2)))
      = (fun i => (A ++ LV).map fun f => rval f (C.co i)) q.2 := by
    intro q hq
    simp only [List.map_append]
    congr 1
    · rw [← listEqF_iff hA, List.map_map]
      refine List.map_congr_left fun b hb => ?_
      exact rval_mix_new (List.all_eq_true.mp hB b hb) _ _
    · refine List.map_congr_left fun f hf => ?_
      obtain ⟨g, hg, hfg⟩ := List.any_eq_true.mp (List.all_eq_true.mp hLV f hf)
      rw [eqF_iff.mp hfg, rval_mix_old (List.all_eq_true.mp hVold g hg)]
      exact key_eq_of_mem hq hg
  show pushEntropy (copySet C.Ω (C.key V)) (copyW C.Ω C.p (C.key V))
    (fun q => (B ++ LV).map fun f => rval f (mix src (C.co q.1) (C.co q.2)))
      = pushEntropy C.Ω C.p (fun i => (A ++ LV).map fun f => rval f (C.co i))
  exact (pushEntropy_congr e).trans
    (pushEntropy_copy_snd hv.nonneg (C.key V) (fun i => (A ++ LV).map fun f => rval f (C.co i)))

/-- **Conditional independence of the copies given `V`.** -/
theorem H_copy_ci (hv : C.Valid Γ) (hVold : V.all (oldF src) = true) (Lold B A : List (Form N))
    (hold : Lold.all (oldF src) = true) (hB : B.all (newF src) = true)
    (hA : listEqF (B.map (pullF src)) A = true) (hAold : A.all (oldF src) = true) :
    (C.copy src V).H (Lold ++ B ++ V) + (C.copy src V).H V
      = (C.copy src V).H (Lold ++ V) + (C.copy src V).H (B ++ V) := by
  have hVV : V.all (fun f => V.any (eqF f)) = true :=
    List.all_eq_true.mpr fun f hf => List.any_eq_true.mpr ⟨f, hf, eqF_iff.mpr rfl⟩
  rw [H_copy_eqlaw hv hVold B V A hB hA hAold hVV]
  have hLV : (Lold ++ V).all (oldF src) = true := by rw [List.all_append, hold, hVold]; rfl
  have hAV : (A ++ V).all (oldF src) = true := by rw [List.all_append, hAold, hVold]; rfl
  rw [H_copy_old hv _ hLV, H_copy_old hv _ hAV, H_copy_old hv _ hVold]
  have hci := pushEntropy_copy_ci hv.nonneg (C.key V) (fun i => Lold.map fun f => rval f (C.co i))
    (fun i => A.map fun f => rval f (C.co i))
  have e : ∀ q ∈ copySet C.Ω (C.key V),
      ((Lold ++ B ++ V).map fun f => rval f (mix src (C.co q.1) (C.co q.2)))
      = (fun x : List ℝ × List ℝ × List ℝ => x.1 ++ x.2.1 ++ x.2.2)
          (Lold.map (fun f => rval f (C.co q.1)), A.map (fun f => rval f (C.co q.2)),
            V.map (fun f => rval f (C.co q.1))) := by
    intro q _
    simp only [List.map_append]
    congr 1
    · congr 1
      · refine List.map_congr_left fun f hf => ?_
        exact rval_mix_old (List.all_eq_true.mp hold f hf) _ _
      · rw [← listEqF_iff hA, List.map_map]
        refine List.map_congr_left fun b hb => ?_
        exact rval_mix_new (List.all_eq_true.mp hB b hb) _ _
    · refine List.map_congr_left fun f hf => ?_
      exact rval_mix_old (List.all_eq_true.mp hVold f hf) _ _
  have hlhs : (C.copy src V).H (Lold ++ B ++ V) = pushEntropy (copySet C.Ω (C.key V)) (copyW C.Ω C.p (C.key V))
      (fun q => (Lold.map (fun f => rval f (C.co q.1)), A.map (fun f => rval f (C.co q.2)),
        V.map (fun f => rval f (C.co q.1)))) := by
    show pushEntropy (copySet C.Ω (C.key V)) (copyW C.Ω C.p (C.key V))
      (fun q => (Lold ++ B ++ V).map fun f => rval f (mix src (C.co q.1) (C.co q.2))) = _
    rw [pushEntropy_congr e]
    refine pushEntropy_eq_of_comp (valid_copy hv src V).nonneg
      (fun y => (y.take Lold.length, (y.drop Lold.length).take A.length, y.drop (Lold.length + A.length)))
      (fun x : List ℝ × List ℝ × List ℝ => x.1 ++ x.2.1 ++ x.2.2) ?_ (fun _ _ => rfl)
    intro q _
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · simp
    · simp
    · simp [List.drop_append]
  have h1 : pushEntropy C.Ω C.p (fun i => (Lold.map (fun f => rval f (C.co i)), C.key V i)) = C.H (Lold ++ V) :=
    H_pair hv.nonneg Lold V
  have h2 : pushEntropy C.Ω C.p (fun i => (A.map (fun f => rval f (C.co i)), C.key V i)) = C.H (A ++ V) :=
    H_pair hv.nonneg A V
  have h3 : pushEntropy C.Ω C.p (C.key V) = C.H V := rfl
  rw [hlhs]
  rw [h1, h2, h3] at hci
  exact hci

/-- **Relations created by a copy step.** -/
theorem rel_copy_new (hVold : V.all (oldF src) = true) {b α r : Form N} (hb : newF src b = true)
    (hα : eqF (pullF src b) α = true) (hαold : oldF src α = true) (hdet : C.Det V α)
    (hr : eqF r (addF b (smulF (-1) α)) = true) : (C.copy src V).Rel r := by
  intro q hq
  obtain ⟨φ, hφ⟩ := hdet
  have hq' := mem_copySet.mp hq
  show rval r (mix src (C.co q.1) (C.co q.2)) = 0
  rw [eqF_iff.mp hr, rval_addF, rval_smulF, rval_mix_new hb, rval_mix_old hαold, eqF_iff.mp hα]
  have h1 := hφ _ hq'.1
  have h2 := hφ _ hq'.2.1
  have hk : (V.map fun c => rval c (C.co q.1)) = V.map fun c => rval c (C.co q.2) := hq'.2.2
  rw [← h1, ← h2, hk]
  push_cast
  ring

end Conf

/-! ## The base configuration: one pair, every vertex equal to it -/

/-- The law `p` on `Γ`, all `N` vertices equal to the pair. -/
abbrev base (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) : Conf N := ⟨ℝ × ℝ, Γ, p, fun q _ => q⟩

theorem valid_base {Γ : Finset (ℝ × ℝ)} {p : ℝ × ℝ → ℝ} (hp : ∀ q ∈ Γ, 0 ≤ p q) (hs : ∑ q ∈ Γ, p q = 1) :
    (base (N := N) Γ p).Valid Γ where
  nonneg := hp
  sum_one := hs
  mem := fun q hq _ => hq

theorem rval_const (f : Form N) (q : ℝ × ℝ) :
    rval f (fun _ => q) = (∑ k, ((f k).1 : ℝ)) * q.1 + (∑ k, ((f k).2 : ℝ)) * q.2 := by
  simp only [rval, Finset.sum_add_distrib, Finset.sum_mul]

end EntropyBounds.Glue
