import SumDifference.MatusInequality

/-!
# A Lean calculus for copy-lemma proofs of linear entropy inequalities

`LSp G n`: a finite weighted space with `n` random variables ("letters") valued in `G`; `X.H S` is the joint
entropy of the letters in `S` (Kleinwaks' `HS`).

`X.copy src ov` is the Zhang–Yeung copy step: a letter `l` with `src l = some u` becomes a copy of `u`, the copies
being conditionally independent of all letters given the letters in `ov` (Kleinwaks' `copySet`/`copyW` over the key
`tup X.v ov`; the copies are read off the second point).  Letters with `src l = none` keep their values.

* `valid_copy`; `H_copy_old` (letters that are not copies keep their joint law); `H_copy_eqlaw` (`(copies, ov)` has
  the law of `(sources, ov)`); `H_copy_ci` (`H(old, new) + H(ov) = H(old) + H(new, ov)`).
* `H_sub`, `H_mono'`, `H_empty'`: elemental Shannon facts.
* `joint`, `H_joint`: joint variables made of sets of letters, to apply a proved inequality to unions of letters.

A proved inequality is stated for every value type `G`, every space and every family of letters; certificates
(check630's "lemma" rows) are turned into such statements and proofs by `tools/export_lemmas.py`.
-/

open Finset

namespace EntropyBounds.Lem

open SumsDifferences SumsDifferences.NonShannon

/-- A finite weighted space with `n` letters valued in `G`. -/
structure LSp (G : Type) (n : ℕ) where
  ι : Type
  s : Finset ι
  p : ι → ℝ
  v : Fin n → ι → G

namespace LSp

variable {G : Type} [DecidableEq G] [Zero G] {n : ℕ}

/-- Joint entropy of the letters in `S`. -/
noncomputable def H (X : LSp G n) (S : Finset (Fin n)) : ℝ := HS X.s X.p X.v S

/-- A probability weight. -/
structure Valid (X : LSp G n) : Prop where
  nonneg : ∀ i ∈ X.s, 0 ≤ X.p i
  sum_one : ∑ i ∈ X.s, X.p i = 1

/-- The letters after a copy step. -/
def copyV {κ : Type} (v : Fin n → κ → G) (src : Fin n → Option (Fin n)) : Fin n → κ × κ → G :=
  fun l q => match src l with
    | some u => v u q.2
    | none => v l q.1

/-- **The copy step.** -/
noncomputable abbrev copy (X : LSp G n) (src : Fin n → Option (Fin n)) (ov : Finset (Fin n)) : LSp G n where
  ι := X.ι × X.ι
  s := copySet X.s (tup X.v ov)
  p := copyW X.s X.p (tup X.v ov)
  v := copyV X.v src

variable {X : LSp G n} {src : Fin n → Option (Fin n)} {ov : Finset (Fin n)}

theorem valid_copy (hX : X.Valid) (src : Fin n → Option (Fin n)) (ov : Finset (Fin n)) :
    (X.copy src ov).Valid where
  nonneg := fun q hq => copyW_nonneg hX.nonneg _ hq
  sum_one := by
    have := copy_sum_fst hX.nonneg (tup X.v ov) (fun _ => (1 : ℝ))
    simp only [mul_one] at this
    show ∑ q ∈ copySet X.s (tup X.v ov), copyW X.s X.p (tup X.v ov) q = 1
    rw [this, hX.sum_one]

theorem copyV_none {κ : Type} {v : Fin n → κ → G} {l : Fin n} (h : src l = none) (q : κ × κ) :
    copyV v src l q = v l q.1 := by
  simp [copyV, h]

theorem copyV_some {κ : Type} {v : Fin n → κ → G} {l u : Fin n} (h : src l = some u) (q : κ × κ) :
    copyV v src l q = v u q.2 := by
  simp [copyV, h]

/-- On the copy set, the letters of `ov` agree at the two points. -/
theorem key_eq {q : X.ι × X.ι} (hq : q ∈ copySet X.s (tup X.v ov)) {l : Fin n} (hl : l ∈ ov) :
    X.v l q.1 = X.v l q.2 := by
  have h := congrFun (mem_copySet.mp hq).2.2 l
  simpa [tup, hl] using h

/-- Letters that are not copies keep their joint law. -/
theorem H_copy_old (hX : X.Valid) (S : Finset (Fin n)) (hS : ∀ l ∈ S, src l = none) :
    (X.copy src ov).H S = X.H S := by
  have e : ∀ q ∈ copySet X.s (tup X.v ov), tup (copyV X.v src) S q = tup X.v S q.1 := by
    intro q _
    funext l
    simp only [tup]
    by_cases hl : l ∈ S
    · rw [if_pos hl, if_pos hl, copyV_none (hS l hl)]
    · rw [if_neg hl, if_neg hl]
  show pushEntropy (copySet X.s (tup X.v ov)) (copyW X.s X.p (tup X.v ov)) (tup (copyV X.v src) S)
    = pushEntropy X.s X.p (tup X.v S)
  exact (pushEntropy_congr e).trans (pushEntropy_copy_fst hX.nonneg (tup X.v ov) (tup X.v S))

/-- A letter of `S` standing for `m` (a copy of `m`, or `m` itself if it is not a copy). -/
noncomputable def pick (S : Finset (Fin n)) (src : Fin n → Option (Fin n)) (m : Fin n) : Fin n :=
  open Classical in
  if h : ∃ l ∈ S, src l = some m ∨ (src l = none ∧ l = m) then h.choose else m

/-- **Equal law of copies and sources**: `H(S) = H(T)` where `T` replaces each copy in `S` by its source; the
letters of `S` that are not copies must lie in `ov`. -/
theorem H_copy_eqlaw (hX : X.Valid) (S T : Finset (Fin n))
    (h1 : ∀ l ∈ S, src l = none → l ∈ ov ∧ l ∈ T) (h2 : ∀ l ∈ S, ∀ u, src l = some u → u ∈ T)
    (h3 : ∀ m ∈ T, ∃ l ∈ S, src l = some m ∨ (src l = none ∧ l = m)) :
    (X.copy src ov).H S = X.H T := by
  classical
  let ψ : (Fin n → G) → (Fin n → G) := fun y l => if l ∈ S then (match src l with
    | some u => y u
    | none => y l) else 0
  let χ : (Fin n → G) → (Fin n → G) := fun z m => if m ∈ T then z (pick S src m) else 0
  have e : ∀ q ∈ copySet X.s (tup X.v ov), tup (copyV X.v src) S q = ψ (tup X.v T q.2) := by
    intro q hq
    funext l
    by_cases hl : l ∈ S
    · rcases hs : src l with _ | u
      · obtain ⟨hlo, hlT⟩ := h1 l hl hs
        have lhs : tup (copyV X.v src) S q l = X.v l q.1 := by
          simp only [tup, if_pos hl, copyV_none hs]
        have rhs : ψ (tup X.v T q.2) l = X.v l q.2 := by
          simp only [ψ, if_pos hl, hs, tup, if_pos hlT]
        rw [lhs, rhs]
        exact key_eq hq hlo
      · have hu := h2 l hl u hs
        have lhs : tup (copyV X.v src) S q l = X.v u q.2 := by
          simp only [tup, if_pos hl, copyV_some hs]
        have rhs : ψ (tup X.v T q.2) l = X.v u q.2 := by
          simp only [ψ, if_pos hl, hs, tup, if_pos hu]
        rw [lhs, rhs]
    · simp only [tup, ψ, if_neg hl]
  have hback : ∀ j, χ (ψ (tup X.v T j)) = tup X.v T j := by
    intro j
    funext m
    by_cases hm : m ∈ T
    · have hex := h3 m hm
      have hpk : pick S src m ∈ S ∧
          (src (pick S src m) = some m ∨ (src (pick S src m) = none ∧ pick S src m = m)) := by
        simp only [pick, dif_pos hex]
        exact hex.choose_spec
      have lhs : χ (ψ (tup X.v T j)) m = ψ (tup X.v T j) (pick S src m) := by
        simp only [χ, if_pos hm]
      rw [lhs]
      rcases hpk.2 with hs | ⟨hs, hpm⟩
      · simp only [ψ, if_pos hpk.1, hs]
      · simp only [ψ, if_pos hpk.1, hs]
        rw [hpm]
    · simp only [χ, tup, if_neg hm]
  show pushEntropy (copySet X.s (tup X.v ov)) (copyW X.s X.p (tup X.v ov)) (tup (copyV X.v src) S)
    = pushEntropy X.s X.p (tup X.v T)
  rw [pushEntropy_congr e, pushEntropy_copy_snd hX.nonneg (tup X.v ov) (fun j => ψ (tup X.v T j))]
  exact pushEntropy_eq_of_comp hX.nonneg χ ψ (fun j _ => hback j) (fun j _ => rfl)

/-- **Conditional independence of the copies given `ov`**: `H(old ∪ new) + H(ov) = H(old) + H(new ∪ ov)` for
`old` without copies, `ov ⊆ old` and `new` made of copies. -/
theorem H_copy_ci (hX : X.Valid) (old nw : Finset (Fin n)) (hold : ∀ l ∈ old, src l = none) (hov : ov ⊆ old)
    (hnw : ∀ l ∈ nw, src l ≠ none) :
    (X.copy src ov).H (old ∪ nw) + (X.copy src ov).H ov = (X.copy src ov).H old + (X.copy src ov).H (nw ∪ ov) := by
  classical
  have hdis : ∀ l ∈ nw, l ∉ old := fun l hl ho => hnw l hl (hold l ho)
  have hdis' : ∀ l ∈ nw, l ∉ ov := fun l hl ho => hdis l hl (hov ho)
  let Gf : X.ι → (Fin n → G) := fun j l => if l ∈ nw then (match src l with
    | some u => X.v u j
    | none => 0) else 0
  have hp' : ∀ q ∈ copySet X.s (tup X.v ov), 0 ≤ copyW X.s X.p (tup X.v ov) q :=
    fun q hq => copyW_nonneg hX.nonneg _ hq
  have key := pushEntropy_copy_ci hX.nonneg (tup X.v ov) (tup X.v old) Gf
  -- the new letters at (i, j) are `Gf j`
  have hG : ∀ q : X.ι × X.ι, ∀ l ∈ nw, copyV X.v src l q = Gf q.2 l := by
    intro q l hl
    simp only [Gf, if_pos hl]
    rcases hs : src l with _ | u
    · exact absurd hs (hnw l hl)
    · simp [copyV, hs]
  have e1 : pushEntropy (copySet X.s (tup X.v ov)) (copyW X.s X.p (tup X.v ov))
      (fun q => (tup X.v old q.1, Gf q.2, tup X.v ov q.1)) = (X.copy src ov).H (old ∪ nw) := by
    show _ = pushEntropy (copySet X.s (tup X.v ov)) (copyW X.s X.p (tup X.v ov)) (tup (copyV X.v src) (old ∪ nw))
    refine pushEntropy_eq_of_comp hp'
      (fun x => fun l => if l ∈ old then x.1 l else if l ∈ nw then x.2.1 l else 0)
      (fun t => (restr old t, restr nw t, restr ov t)) ?_ ?_
    · intro q _
      funext l
      simp only [tup, Finset.mem_union]
      by_cases ho : l ∈ old
      · simp [ho, copyV_none (hold l ho)]
      · by_cases hn : l ∈ nw
        · simp only [ho, if_false, hn, if_true, or_true]
          rw [hG q l hn]
        · simp [ho, hn]
    · intro q _
      simp only [Prod.mk.injEq]
      refine ⟨?_, ?_, ?_⟩
      · funext l; simp only [restr, tup, Finset.mem_union]
        by_cases ho : l ∈ old
        · simp [ho, copyV_none (hold l ho)]
        · simp [ho]
      · funext l; simp only [restr, tup, Finset.mem_union]
        by_cases hn : l ∈ nw
        · simp only [hn, if_true, or_true]
          exact hG q l hn
        · simp [hn, Gf]
      · funext l; simp only [restr, tup, Finset.mem_union]
        by_cases ho : l ∈ ov
        · simp [ho, hov ho, copyV_none (hold l (hov ho))]
        · simp [ho]
  have e2 : pushEntropy X.s X.p (fun i => (tup X.v old i, tup X.v ov i)) = (X.copy src ov).H old := by
    rw [H_copy_old hX old hold]
    refine pushEntropy_eq_of_comp hX.nonneg (fun x => x.1) (fun t => (t, restr ov t)) (fun _ _ => rfl) ?_
    intro i _
    exact Prod.ext rfl (restr_tup X.v hov i)
  have e3 : pushEntropy X.s X.p (tup X.v ov) = (X.copy src ov).H ov := by
    rw [H_copy_old hX ov (fun l hl => hold l (hov hl))]
    rfl
  have e4 : pushEntropy X.s X.p (fun i => (Gf i, tup X.v ov i)) = (X.copy src ov).H (nw ∪ ov) := by
    have ec : ∀ q ∈ copySet X.s (tup X.v ov), tup (copyV X.v src) (nw ∪ ov) q
        = (fun x : (Fin n → G) × (Fin n → G) => fun l => if l ∈ nw then x.1 l else x.2 l)
            (Gf q.2, tup X.v ov q.2) := by
      intro q hq
      funext l
      simp only [tup, Finset.mem_union]
      by_cases hn : l ∈ nw
      · simp only [hn, true_or, if_true]
        exact hG q l hn
      · by_cases ho : l ∈ ov
        · simp only [hn, false_or, ho, if_true, if_false]
          rw [copyV_none (hold l (hov ho))]
          exact key_eq hq ho
        · simp [hn, ho]
    symm
    show pushEntropy (copySet X.s (tup X.v ov)) (copyW X.s X.p (tup X.v ov)) (tup (copyV X.v src) (nw ∪ ov)) = _
    rw [pushEntropy_congr ec, pushEntropy_copy_snd hX.nonneg (tup X.v ov)
      (fun j => (fun x : (Fin n → G) × (Fin n → G) => fun l => if l ∈ nw then x.1 l else x.2 l) (Gf j, tup X.v ov j))]
    refine pushEntropy_eq_of_comp hX.nonneg (fun t => (restr nw t, restr ov t))
      (fun x : (Fin n → G) × (Fin n → G) => fun l => if l ∈ nw then x.1 l else x.2 l) ?_ ?_
    · intro j _
      simp only [Prod.mk.injEq]
      refine ⟨?_, ?_⟩
      · funext l; simp only [restr]
        by_cases hn : l ∈ nw
        · simp [hn]
        · simp [hn, Gf]
      · funext l; simp only [restr, tup]
        by_cases ho : l ∈ ov
        · simp only [ho, if_true]
          rw [if_neg (fun hn => hdis' l hn ho)]
        · simp only [ho, if_false]
    · intro j _
      rfl
  rw [e1, e2, e3, e4] at key
  linarith

/-- `H_copy_ci` with the two unions given as literals. -/
theorem H_copy_ci' (hX : X.Valid) (old nw A₁ A₄ : Finset (Fin n)) (hold : ∀ l ∈ old, src l = none) (hov : ov ⊆ old)
    (hnw : ∀ l ∈ nw, src l ≠ none) (h₁ : old ∪ nw = A₁) (h₄ : nw ∪ ov = A₄) :
    (X.copy src ov).H A₁ + (X.copy src ov).H ov = (X.copy src ov).H old + (X.copy src ov).H A₄ := by
  rw [← h₁, ← h₄]
  exact H_copy_ci hX old nw hold hov hnw

/-! ## Shannon facts -/

theorem H_sub (hX : X.Valid) {S T U V : Finset (Fin n)} (hU : S ∪ T = U) (hV : S ∩ T = V) :
    X.H U + X.H V ≤ X.H S + X.H T :=
  HS_submod_lit hX.nonneg hX.sum_one X.v hU hV

theorem H_mono' (hX : X.Valid) {S T : Finset (Fin n)} (h : S ⊆ T) : X.H S ≤ X.H T :=
  HS_mono hX.nonneg X.v h

theorem H_empty' (hX : X.Valid) : X.H ∅ = 0 := HS_empty hX.nonneg hX.sum_one X.v

/-! ## Joint variables -/

/-- Letters `j < m` of a new family: the joint variables of the sets `A j`. -/
abbrev joint {m : ℕ} (X : LSp G n) (A : Fin m → Finset (Fin n)) : LSp (Fin n → G) m :=
  ⟨X.ι, X.s, X.p, fun j i => tup X.v (A j) i⟩

theorem valid_joint {m : ℕ} (hX : X.Valid) (A : Fin m → Finset (Fin n)) : (X.joint A).Valid :=
  ⟨hX.nonneg, hX.sum_one⟩

/-- The joint entropy of joint variables is the joint entropy of the union. -/
theorem H_joint {m : ℕ} (hX : X.Valid) (A : Fin m → Finset (Fin n)) (T : Finset (Fin m)) (U : Finset (Fin n))
    (hU : T.biUnion A = U) : (X.joint A).H T = X.H U := by
  classical
  subst hU
  show pushEntropy X.s X.p (tup (fun j i => tup X.v (A j) i) T) = pushEntropy X.s X.p (tup X.v (T.biUnion A))
  refine pushEntropy_eq_of_comp hX.nonneg
    (fun z => fun l => if h : ∃ j ∈ T, l ∈ A j then z h.choose l else 0)
    (fun y => fun j => if j ∈ T then restr (A j) y else 0) ?_ ?_
  · intro i _
    funext l
    by_cases h : ∃ j ∈ T, l ∈ A j
    · rw [dif_pos h]
      have hm : l ∈ T.biUnion A := Finset.mem_biUnion.mpr h
      simp only [tup, if_pos h.choose_spec.1, if_pos h.choose_spec.2, if_pos hm]
    · rw [dif_neg h]
      have hm : l ∉ T.biUnion A := fun hm => h (Finset.mem_biUnion.mp hm)
      simp only [tup, if_neg hm]
  · intro i _
    funext j
    by_cases hj : j ∈ T
    · simp only [tup, if_pos hj]
      funext l
      simp only [restr, tup]
      by_cases hl : l ∈ A j
      · have hm : l ∈ T.biUnion A := Finset.mem_biUnion.mpr ⟨j, hj, hl⟩
        simp only [if_pos hl, if_pos hm]
      · simp only [if_neg hl]
    · simp only [tup, if_neg hj]

end LSp

end EntropyBounds.Lem
