import EntropyBounds.GlueZ.Certs.C3BALL.Defs

set_option linter.unusedVariables false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open Finset

/-! The glued configuration of `c3b_allgroups.json`: copy steps, validity, relations (proved), lifts. -/

namespace EntropyBounds.GlueZ.Certs.C3BALL

variable {G : Type} [AddCommGroup G] [DecidableEq G]

open EntropyBounds.Iid EntropyBounds.GlueG EntropyBounds.GlueZ SumsDifferences SumsDifferences.NonShannon

/-- Step 0: copies of the vertices [0] at [1] over the key [(0, (1, 0))]. -/
def src0 : Fin 6 → Option (Fin 6) := ![none, some 0, none, none, none, none]

def V0 : List (Form 6) := L1

/-- Step 1: copies of the vertices [0, 1] at [2, 3] over the key [(0, (0, 1)), (1, (0, 1))]. -/
def src1 : Fin 6 → Option (Fin 6) := ![none, none, some 0, some 1, none, none]

def V1 : List (Form 6) := L52

/-- Step 2: copies of the vertices [0, 1] at [4, 5] over the key [(0, (1, 1)), (1, (0, 1))]. -/
def src2 : Fin 6 → Option (Fin 6) := ![none, none, none, none, some 0, some 1]

def V2 : List (Form 6) := L56

/-- The glued configurations. -/
noncomputable abbrev C0 (Γ : Finset (G × G)) (p : G × G → ℝ) : Conf 6 G := base Γ p

noncomputable abbrev C1 (Γ : Finset (G × G)) (p : G × G → ℝ) : Conf 6 G := (C0 Γ p).copy src0 V0

noncomputable abbrev C2 (Γ : Finset (G × G)) (p : G × G → ℝ) : Conf 6 G := (C1 Γ p).copy src1 V1

noncomputable abbrev C3 (Γ : Finset (G × G)) (p : G × G → ℝ) : Conf 6 G := (C2 Γ p).copy src2 V2

noncomputable abbrev CF (Γ : Finset (G × G)) (p : G × G → ℝ) : Conf 6 G := C3 Γ p

theorem hv0 {Γ : Finset (G × G)} {p : G × G → ℝ} (h : HypZ Γ p) : (C0 Γ p).Valid Γ :=
  valid_base h.nonneg h.sum_one

theorem hv1 {Γ : Finset (G × G)} {p : G × G → ℝ} (h : HypZ Γ p) : (C1 Γ p).Valid Γ :=
  Conf.valid_copy (hv0 h) src0 V0

theorem hv2 {Γ : Finset (G × G)} {p : G × G → ℝ} (h : HypZ Γ p) : (C2 Γ p).Valid Γ :=
  Conf.valid_copy (hv1 h) src1 V1

theorem hv3 {Γ : Finset (G × G)} {p : G × G → ℝ} (h : HypZ Γ p) : (C3 Γ p).Valid Γ :=
  Conf.valid_copy (hv2 h) src2 V2

theorem hvF {Γ : Finset (G × G)} {p : G × G → ℝ} (h : HypZ Γ p) : (CF Γ p).Valid Γ := hv3 h

def R0 : List (Form 6) := []

theorem rel0 {Γ : Finset (G × G)} {p : G × G → ℝ} (h : HypZ Γ p) : ∀ r ∈ R0, (C0 Γ p).Rel r := by
  intro r hr; exact absurd hr List.not_mem_nil

theorem newrel0_0 {Γ : Finset (G × G)} {p : G × G → ℝ} (h : HypZ Γ p) : (C1 Γ p).Rel F44 := by
  have da : (C0 Γ p).Det L1 F1 :=
    Conf.det_of_checkDWR1 h.inj (hv0 h) (rel0 h) (w := ⟨1, [1], [], ![(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0)], ![1, 1, 1, 1, 1, 1], ![[], [], [], [], [], []], ![[], [], [], [], [], []]⟩) (by decide)
  have dV : (C0 Γ p).Det V0 F1 := da
  exact Conf.rel_copy_new (src := src0) (V := V0) (by decide) (b := F0) (α := F1) (by decide) (by decide)
    (by decide) dV (by decide)

def R1 : List (Form 6) := R0 ++ [F44]

theorem rel1 {Γ : Finset (G × G)} {p : G × G → ℝ} (h : HypZ Γ p) : ∀ r ∈ R1, (C1 Γ p).Rel r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact Conf.rel_copy_old (rel0 h r hr) (List.all_eq_true.mp (show R0.all (oldF src0) = true by decide) r hr)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · exact newrel0_0 h

theorem newrel1_0 {Γ : Finset (G × G)} {p : G × G → ℝ} (h : HypZ Γ p) : (C2 Γ p).Rel F45 := by
  have da : (C1 Γ p).Det L52 F27 :=
    Conf.det_of_checkDWR1 h.inj (hv1 h) (rel1 h) (w := ⟨1, [0, 1], [0], ![(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0)], ![1, 1, 1, 1, 1, 1], ![[], [], [], [], [], []], ![[], [], [], [], [], []]⟩) (by decide)
  have dV : (C1 Γ p).Det V1 F27 := da
  exact Conf.rel_copy_new (src := src1) (V := V1) (by decide) (b := F25) (α := F27) (by decide) (by decide)
    (by decide) dV (by decide)

theorem newrel1_1 {Γ : Finset (G × G)} {p : G × G → ℝ} (h : HypZ Γ p) : (C2 Γ p).Rel F46 := by
  have da : (C1 Γ p).Det L52 F5 :=
    Conf.det_of_checkDWR1 h.inj (hv1 h) (rel1 h) (w := ⟨1, [1, 0], [0], ![(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0)], ![1, 1, 1, 1, 1, 1], ![[], [], [], [], [], []], ![[], [], [], [], [], []]⟩) (by decide)
  have dV : (C1 Γ p).Det V1 F5 := da
  exact Conf.rel_copy_new (src := src1) (V := V1) (by decide) (b := F4) (α := F5) (by decide) (by decide)
    (by decide) dV (by decide)

theorem newrel1_2 {Γ : Finset (G × G)} {p : G × G → ℝ} (h : HypZ Γ p) : (C2 Γ p).Rel F48 := by
  have da : (C1 Γ p).Det L52 F47 :=
    Conf.det_of_checkDWR1 h.inj (hv1 h) (rel1 h) (w := ⟨1, [0, 0], [-1], ![(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0)], ![1, 1, 1, 1, 1, 1], ![[], [], [], [], [], []], ![[], [], [], [], [], []]⟩) (by decide)
  have dV : (C1 Γ p).Det V1 F47 := da
  exact Conf.rel_copy_new (src := src1) (V := V1) (by decide) (b := F49) (α := F47) (by decide) (by decide)
    (by decide) dV (by decide)

def R2 : List (Form 6) := R1 ++ [F45, F46, F48]

theorem rel2 {Γ : Finset (G × G)} {p : G × G → ℝ} (h : HypZ Γ p) : ∀ r ∈ R2, (C2 Γ p).Rel r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact Conf.rel_copy_old (rel1 h r hr) (List.all_eq_true.mp (show R1.all (oldF src1) = true by decide) r hr)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact newrel1_0 h
    · exact newrel1_1 h
    · exact newrel1_2 h

theorem newrel2_0 {Γ : Finset (G × G)} {p : G × G → ℝ} (h : HypZ Γ p) : (C3 Γ p).Rel F50 := by
  have da : (C2 Γ p).Det L56 F47 :=
    Conf.det_of_checkDWR1 h.inj (hv2 h) (rel2 h) (w := ⟨1, [0, 0], [-1, 0, 0, 0], ![(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0)], ![1, 1, 1, 1, 1, 1], ![[], [], [], [], [], []], ![[], [], [], [], [], []]⟩) (by decide)
  have dV : (C2 Γ p).Det V2 F47 := da
  exact Conf.rel_copy_new (src := src2) (V := V2) (by decide) (b := F51) (α := F47) (by decide) (by decide)
    (by decide) dV (by decide)

theorem newrel2_1 {Γ : Finset (G × G)} {p : G × G → ℝ} (h : HypZ Γ p) : (C3 Γ p).Rel F52 := by
  have da : (C2 Γ p).Det L56 F27 :=
    Conf.det_of_checkDWR1 h.inj (hv2 h) (rel2 h) (w := ⟨1, [0, 1], [0, 0, 0, 0], ![(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0)], ![1, 1, 1, 1, 1, 1], ![[], [], [], [], [], []], ![[], [], [], [], [], []]⟩) (by decide)
  have dV : (C2 Γ p).Det V2 F27 := da
  exact Conf.rel_copy_new (src := src2) (V := V2) (by decide) (b := F24) (α := F27) (by decide) (by decide)
    (by decide) dV (by decide)

theorem newrel2_2 {Γ : Finset (G × G)} {p : G × G → ℝ} (h : HypZ Γ p) : (C3 Γ p).Rel F54 := by
  have da : (C2 Γ p).Det L56 F53 :=
    Conf.det_of_checkDWR1 h.inj (hv2 h) (rel2 h) (w := ⟨1, [1, 0], [1, 0, 0, 0], ![(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0)], ![1, 1, 1, 1, 1, 1], ![[], [], [], [], [], []], ![[], [], [], [], [], []]⟩) (by decide)
  have dV : (C2 Γ p).Det V2 F53 := da
  exact Conf.rel_copy_new (src := src2) (V := V2) (by decide) (b := F55) (α := F53) (by decide) (by decide)
    (by decide) dV (by decide)

def R3 : List (Form 6) := R2 ++ [F50, F52, F54]

theorem rel3 {Γ : Finset (G × G)} {p : G × G → ℝ} (h : HypZ Γ p) : ∀ r ∈ R3, (C3 Γ p).Rel r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact Conf.rel_copy_old (rel2 h r hr) (List.all_eq_true.mp (show R2.all (oldF src2) = true by decide) r hr)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact newrel2_0 h
    · exact newrel2_1 h
    · exact newrel2_2 h

def RF : List (Form 6) := R3

theorem relF {Γ : Finset (G × G)} {p : G × G → ℝ} (h : HypZ Γ p) : ∀ r ∈ RF, (CF Γ p).Rel r := rel3 h

theorem lift1 {Γ : Finset (G × G)} {p : G × G → ℝ} (h : HypZ Γ p) (l : List (Form 6)) (h1 : l.all (oldF src1) = true) (h2 : l.all (oldF src2) = true) :
    (CF Γ p).H l = (C1 Γ p).H l := by
  show (C3 Γ p).H l = _
  rw [show (C3 Γ p).H l = (C2 Γ p).H l from Conf.H_copy_old (hv2 h) l h2]
  rw [show (C2 Γ p).H l = (C1 Γ p).H l from Conf.H_copy_old (hv1 h) l h1]

theorem lift2 {Γ : Finset (G × G)} {p : G × G → ℝ} (h : HypZ Γ p) (l : List (Form 6)) (h2 : l.all (oldF src2) = true) :
    (CF Γ p).H l = (C2 Γ p).H l := by
  show (C3 Γ p).H l = _
  rw [show (C3 Γ p).H l = (C2 Γ p).H l from Conf.H_copy_old (hv2 h) l h2]

theorem lift0 {Γ : Finset (G × G)} {p : G × G → ℝ} (h : HypZ Γ p) (l : List (Form 6)) (h0 : l.all (oldF src0) = true) (h1 : l.all (oldF src1) = true) (h2 : l.all (oldF src2) = true) :
    (CF Γ p).H l = (C0 Γ p).H l := by
  show (C3 Γ p).H l = _
  rw [show (C3 Γ p).H l = (C2 Γ p).H l from Conf.H_copy_old (hv2 h) l h2]
  rw [show (C2 Γ p).H l = (C1 Γ p).H l from Conf.H_copy_old (hv1 h) l h1]
  rw [show (C1 Γ p).H l = (C0 Γ p).H l from Conf.H_copy_old (hv0 h) l h0]

end EntropyBounds.GlueZ.Certs.C3BALL
