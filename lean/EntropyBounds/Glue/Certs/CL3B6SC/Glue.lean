import EntropyBounds.Glue.Certs.CL3B6SC.Defs

set_option linter.unusedVariables false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open Finset

/-! The glued configuration of `c3b_torsionfree.json`: copy steps, validity, relations (proved), lifts. -/

namespace EntropyBounds.Glue.Certs.CL3B6SC

open EntropyBounds.Iid EntropyBounds.Glue SumsDifferences SumsDifferences.NonShannon

/-- Step 0: copies of the vertices [0] at [1] over the key [(0, (1, 0))]. -/
def src0 : Fin 6 → Option (Fin 6) := ![none, some 0, none, none, none, none]

def V0 : List (Form 6) := L17

/-- Step 1: copies of the vertices [0, 1] at [2, 3] over the key [(0, (0, 1)), (1, (0, 1))]. -/
def src1 : Fin 6 → Option (Fin 6) := ![none, none, some 0, some 1, none, none]

def V1 : List (Form 6) := L108

/-- Step 2: copies of the vertices [0, 1] at [4, 5] over the key [(0, (1, 1)), (1, (0, 1))]. -/
def src2 : Fin 6 → Option (Fin 6) := ![none, none, none, none, some 0, some 1]

def V2 : List (Form 6) := L112

/-- The glued configurations. -/
noncomputable abbrev C0 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) : Conf 6 := base Γ p

noncomputable abbrev C1 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) : Conf 6 := (C0 Γ p).copy src0 V0

noncomputable abbrev C2 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) : Conf 6 := (C1 Γ p).copy src1 V1

noncomputable abbrev C3 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) : Conf 6 := (C2 Γ p).copy src2 V2

noncomputable abbrev CF (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) : Conf 6 := C3 Γ p

theorem hv0 {Γ : Finset (ℝ × ℝ)} {p : ℝ × ℝ → ℝ} (h : Hyp Γ p) : (C0 Γ p).Valid Γ :=
  valid_base h.nonneg h.sum_one

theorem hv1 {Γ : Finset (ℝ × ℝ)} {p : ℝ × ℝ → ℝ} (h : Hyp Γ p) : (C1 Γ p).Valid Γ :=
  Conf.valid_copy (hv0 h) src0 V0

theorem hv2 {Γ : Finset (ℝ × ℝ)} {p : ℝ × ℝ → ℝ} (h : Hyp Γ p) : (C2 Γ p).Valid Γ :=
  Conf.valid_copy (hv1 h) src1 V1

theorem hv3 {Γ : Finset (ℝ × ℝ)} {p : ℝ × ℝ → ℝ} (h : Hyp Γ p) : (C3 Γ p).Valid Γ :=
  Conf.valid_copy (hv2 h) src2 V2

theorem hvF {Γ : Finset (ℝ × ℝ)} {p : ℝ × ℝ → ℝ} (h : Hyp Γ p) : (CF Γ p).Valid Γ := hv3 h

def R0 : List (Form 6) := []

theorem rel0 {Γ : Finset (ℝ × ℝ)} {p : ℝ × ℝ → ℝ} (h : Hyp Γ p) : ∀ r ∈ R0, (C0 Γ p).Rel r := by
  intro r hr; exact absurd hr List.not_mem_nil

theorem newrel0_0 {Γ : Finset (ℝ × ℝ)} {p : ℝ × ℝ → ℝ} (h : Hyp Γ p) : (C1 Γ p).Rel F152 := by
  have da : (C0 Γ p).Det L17 F10 :=
    Conf.det_of_checkDWR h.inj (hv0 h) (rel0 h) (w := ⟨1, [1], [], ![(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0)], ![1, 1, 1, 1, 1, 1], ![[], [], [], [], [], []], ![[], [], [], [], [], []]⟩) (by decide)
  have dV : (C0 Γ p).Det V0 F10 := da
  exact Conf.rel_copy_new (src := src0) (V := V0) (by decide) (b := F57) (α := F10) (by decide) (by decide)
    (by decide) dV (by decide)

def R1 : List (Form 6) := R0 ++ [F152]

theorem rel1 {Γ : Finset (ℝ × ℝ)} {p : ℝ × ℝ → ℝ} (h : Hyp Γ p) : ∀ r ∈ R1, (C1 Γ p).Rel r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact Conf.rel_copy_old (rel0 h r hr) (List.all_eq_true.mp (show R0.all (oldF src0) = true by decide) r hr)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · exact newrel0_0 h

theorem newrel1_0 {Γ : Finset (ℝ × ℝ)} {p : ℝ × ℝ → ℝ} (h : Hyp Γ p) : (C2 Γ p).Rel F153 := by
  have da : (C1 Γ p).Det L108 F7 :=
    Conf.det_of_checkDWR h.inj (hv1 h) (rel1 h) (w := ⟨1, [0, 1], [0], ![(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0)], ![1, 1, 1, 1, 1, 1], ![[], [], [], [], [], []], ![[], [], [], [], [], []]⟩) (by decide)
  have dV : (C1 Γ p).Det V1 F7 := da
  exact Conf.rel_copy_new (src := src1) (V := V1) (by decide) (b := F54) (α := F7) (by decide) (by decide)
    (by decide) dV (by decide)

theorem newrel1_1 {Γ : Finset (ℝ × ℝ)} {p : ℝ × ℝ → ℝ} (h : Hyp Γ p) : (C2 Γ p).Rel F154 := by
  have da : (C1 Γ p).Det L108 F6 :=
    Conf.det_of_checkDWR h.inj (hv1 h) (rel1 h) (w := ⟨1, [1, 0], [0], ![(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0)], ![1, 1, 1, 1, 1, 1], ![[], [], [], [], [], []], ![[], [], [], [], [], []]⟩) (by decide)
  have dV : (C1 Γ p).Det V1 F6 := da
  exact Conf.rel_copy_new (src := src1) (V := V1) (by decide) (b := F1) (α := F6) (by decide) (by decide)
    (by decide) dV (by decide)

theorem newrel1_2 {Γ : Finset (ℝ × ℝ)} {p : ℝ × ℝ → ℝ} (h : Hyp Γ p) : (C2 Γ p).Rel F156 := by
  have da : (C1 Γ p).Det L108 F155 :=
    Conf.det_of_checkDWR h.inj (hv1 h) (rel1 h) (w := ⟨1, [0, 0], [-1], ![(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0)], ![1, 1, 1, 1, 1, 1], ![[], [], [], [], [], []], ![[], [], [], [], [], []]⟩) (by decide)
  have dV : (C1 Γ p).Det V1 F155 := da
  exact Conf.rel_copy_new (src := src1) (V := V1) (by decide) (b := F157) (α := F155) (by decide) (by decide)
    (by decide) dV (by decide)

def R2 : List (Form 6) := R1 ++ [F153, F154, F156]

theorem rel2 {Γ : Finset (ℝ × ℝ)} {p : ℝ × ℝ → ℝ} (h : Hyp Γ p) : ∀ r ∈ R2, (C2 Γ p).Rel r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact Conf.rel_copy_old (rel1 h r hr) (List.all_eq_true.mp (show R1.all (oldF src1) = true by decide) r hr)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact newrel1_0 h
    · exact newrel1_1 h
    · exact newrel1_2 h

theorem newrel2_0 {Γ : Finset (ℝ × ℝ)} {p : ℝ × ℝ → ℝ} (h : Hyp Γ p) : (C3 Γ p).Rel F158 := by
  have da : (C2 Γ p).Det L112 F155 :=
    Conf.det_of_checkDWR h.inj (hv2 h) (rel2 h) (w := ⟨1, [0, 0], [-1, 0, 0, 0], ![(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0)], ![1, 1, 1, 1, 1, 1], ![[], [], [], [], [], []], ![[], [], [], [], [], []]⟩) (by decide)
  have dV : (C2 Γ p).Det V2 F155 := da
  exact Conf.rel_copy_new (src := src2) (V := V2) (by decide) (b := F159) (α := F155) (by decide) (by decide)
    (by decide) dV (by decide)

theorem newrel2_1 {Γ : Finset (ℝ × ℝ)} {p : ℝ × ℝ → ℝ} (h : Hyp Γ p) : (C3 Γ p).Rel F160 := by
  have da : (C2 Γ p).Det L112 F7 :=
    Conf.det_of_checkDWR h.inj (hv2 h) (rel2 h) (w := ⟨1, [0, 1], [0, 0, 0, 0], ![(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0)], ![1, 1, 1, 1, 1, 1], ![[], [], [], [], [], []], ![[], [], [], [], [], []]⟩) (by decide)
  have dV : (C2 Γ p).Det V2 F7 := da
  exact Conf.rel_copy_new (src := src2) (V := V2) (by decide) (b := F2) (α := F7) (by decide) (by decide)
    (by decide) dV (by decide)

theorem newrel2_2 {Γ : Finset (ℝ × ℝ)} {p : ℝ × ℝ → ℝ} (h : Hyp Γ p) : (C3 Γ p).Rel F162 := by
  have da : (C2 Γ p).Det L112 F161 :=
    Conf.det_of_checkDWR h.inj (hv2 h) (rel2 h) (w := ⟨1, [1, 0], [1, 0, 0, 0], ![(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0)], ![1, 1, 1, 1, 1, 1], ![[], [], [], [], [], []], ![[], [], [], [], [], []]⟩) (by decide)
  have dV : (C2 Γ p).Det V2 F161 := da
  exact Conf.rel_copy_new (src := src2) (V := V2) (by decide) (b := F40) (α := F161) (by decide) (by decide)
    (by decide) dV (by decide)

def R3 : List (Form 6) := R2 ++ [F158, F160, F162]

theorem rel3 {Γ : Finset (ℝ × ℝ)} {p : ℝ × ℝ → ℝ} (h : Hyp Γ p) : ∀ r ∈ R3, (C3 Γ p).Rel r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact Conf.rel_copy_old (rel2 h r hr) (List.all_eq_true.mp (show R2.all (oldF src2) = true by decide) r hr)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact newrel2_0 h
    · exact newrel2_1 h
    · exact newrel2_2 h

def RF : List (Form 6) := R3

theorem relF {Γ : Finset (ℝ × ℝ)} {p : ℝ × ℝ → ℝ} (h : Hyp Γ p) : ∀ r ∈ RF, (CF Γ p).Rel r := rel3 h

theorem lift1 {Γ : Finset (ℝ × ℝ)} {p : ℝ × ℝ → ℝ} (h : Hyp Γ p) (l : List (Form 6)) (h1 : l.all (oldF src1) = true) (h2 : l.all (oldF src2) = true) :
    (CF Γ p).H l = (C1 Γ p).H l := by
  show (C3 Γ p).H l = _
  rw [show (C3 Γ p).H l = (C2 Γ p).H l from Conf.H_copy_old (hv2 h) l h2]
  rw [show (C2 Γ p).H l = (C1 Γ p).H l from Conf.H_copy_old (hv1 h) l h1]

theorem lift2 {Γ : Finset (ℝ × ℝ)} {p : ℝ × ℝ → ℝ} (h : Hyp Γ p) (l : List (Form 6)) (h2 : l.all (oldF src2) = true) :
    (CF Γ p).H l = (C2 Γ p).H l := by
  show (C3 Γ p).H l = _
  rw [show (C3 Γ p).H l = (C2 Γ p).H l from Conf.H_copy_old (hv2 h) l h2]

theorem lift0 {Γ : Finset (ℝ × ℝ)} {p : ℝ × ℝ → ℝ} (h : Hyp Γ p) (l : List (Form 6)) (h0 : l.all (oldF src0) = true) (h1 : l.all (oldF src1) = true) (h2 : l.all (oldF src2) = true) :
    (CF Γ p).H l = (C0 Γ p).H l := by
  show (C3 Γ p).H l = _
  rw [show (C3 Γ p).H l = (C2 Γ p).H l from Conf.H_copy_old (hv2 h) l h2]
  rw [show (C2 Γ p).H l = (C1 Γ p).H l from Conf.H_copy_old (hv1 h) l h1]
  rw [show (C1 Γ p).H l = (C0 Γ p).H l from Conf.H_copy_old (hv0 h) l h0]

end EntropyBounds.Glue.Certs.CL3B6SC
