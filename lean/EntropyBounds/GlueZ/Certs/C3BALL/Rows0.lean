import EntropyBounds.GlueZ.Certs.C3BALL.Ids0
import EntropyBounds.GlueZ.Certs.C3BALL.Ids1

set_option linter.unusedVariables false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open Finset

namespace EntropyBounds.GlueZ.Certs.C3BALL

variable {G : Type} [AddCommGroup G] [DecidableEq G]

open EntropyBounds.Iid EntropyBounds.GlueG EntropyBounds.GlueZ SumsDifferences SumsDifferences.NonShannon

theorem row0 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L0 + (1 : ℝ) * (CF Γ p).H L2 + (-1 : ℝ) * (CF Γ p).H L3 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F1] ([] : List (Form 6)) [F2]
  rw [show [F1] ++ ([] : List (Form 6)) ++ [F2] = L4 from rfl, show [F1] ++ ([] : List (Form 6)) = L1 from rfl,
    show ([] : List (Form 6)) ++ [F2] = L2 from rfl] at hh
  rw [i1 h, i0 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row1 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L5 + (1 : ℝ) * (CF Γ p).H L7 + (-1 : ℝ) * (CF Γ p).H L9 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F5] ([] : List (Form 6)) [F7]
  rw [show [F5] ++ ([] : List (Form 6)) ++ [F7] = L10 from rfl, show [F5] ++ ([] : List (Form 6)) = L6 from rfl,
    show ([] : List (Form 6)) ++ [F7] = L8 from rfl] at hh
  rw [i4 h, i2 h, i3 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row2 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L0 + (1 : ℝ) * (CF Γ p).H L11 + (-1 : ℝ) * (CF Γ p).H L12 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F1] ([] : List (Form 6)) [F8]
  rw [show [F1] ++ ([] : List (Form 6)) ++ [F8] = L13 from rfl, show [F1] ++ ([] : List (Form 6)) = L1 from rfl,
    show ([] : List (Form 6)) ++ [F8] = L11 from rfl] at hh
  rw [i5 h, i0 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row3 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L0 + (1 : ℝ) * (CF Γ p).H L14 + (-1 : ℝ) * (CF Γ p).H L15 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F1] ([] : List (Form 6)) [F11]
  rw [show [F1] ++ ([] : List (Form 6)) ++ [F11] = L16 from rfl, show [F1] ++ ([] : List (Form 6)) = L1 from rfl,
    show ([] : List (Form 6)) ++ [F11] = L14 from rfl] at hh
  rw [i6 h, i0 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row4 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L17 + (1 : ℝ) * (CF Γ p).H L19 + (-1 : ℝ) * (CF Γ p).H L21 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F14] ([] : List (Form 6)) [F16]
  rw [show [F14] ++ ([] : List (Form 6)) ++ [F16] = L22 from rfl, show [F14] ++ ([] : List (Form 6)) = L18 from rfl,
    show ([] : List (Form 6)) ++ [F16] = L20 from rfl] at hh
  rw [i9 h, i7 h, i8 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row5 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L23 + (1 : ℝ) * (CF Γ p).H L19 + (-1 : ℝ) * (CF Γ p).H L24 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F18] ([] : List (Form 6)) [F16]
  rw [show [F18] ++ ([] : List (Form 6)) ++ [F16] = L25 from rfl, show [F18] ++ ([] : List (Form 6)) = L23 from rfl,
    show ([] : List (Form 6)) ++ [F16] = L20 from rfl] at hh
  rw [i10 h, i8 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row6 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L23 + (1 : ℝ) * (CF Γ p).H L7 + (-1 : ℝ) * (CF Γ p).H L26 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F18] ([] : List (Form 6)) [F7]
  rw [show [F18] ++ ([] : List (Form 6)) ++ [F7] = L27 from rfl, show [F18] ++ ([] : List (Form 6)) = L23 from rfl,
    show ([] : List (Form 6)) ++ [F7] = L8 from rfl] at hh
  rw [i11 h, i3 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row7 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L19 + (1 : ℝ) * (CF Γ p).H L28 + (-1 : ℝ) * (CF Γ p).H L29 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F16] ([] : List (Form 6)) [F9]
  rw [show [F16] ++ ([] : List (Form 6)) ++ [F9] = L30 from rfl, show [F16] ++ ([] : List (Form 6)) = L20 from rfl,
    show ([] : List (Form 6)) ++ [F9] = L28 from rfl] at hh
  rw [i12 h, i8 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row8 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L0 + (1 : ℝ) * (CF Γ p).H L32 + (-1 : ℝ) * (CF Γ p).H L29 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F1] ([] : List (Form 6)) [F17]
  rw [show [F1] ++ ([] : List (Form 6)) ++ [F17] = L33 from rfl, show [F1] ++ ([] : List (Form 6)) = L1 from rfl,
    show ([] : List (Form 6)) ++ [F17] = L32 from rfl] at hh
  rw [i13 h, i0 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row9 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L0 + (1 : ℝ) * (CF Γ p).H L35 + (-1 : ℝ) * (CF Γ p).H L36 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F1] ([] : List (Form 6)) [F19]
  rw [show [F1] ++ ([] : List (Form 6)) ++ [F19] = L37 from rfl, show [F1] ++ ([] : List (Form 6)) = L1 from rfl,
    show ([] : List (Form 6)) ++ [F19] = L35 from rfl] at hh
  rw [i14 h, i0 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row10 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L0 + (1 : ℝ) * (CF Γ p).H L39 + (-1 : ℝ) * (CF Γ p).H L40 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F1] ([] : List (Form 6)) [F20]
  rw [show [F1] ++ ([] : List (Form 6)) ++ [F20] = L41 from rfl, show [F1] ++ ([] : List (Form 6)) = L1 from rfl,
    show ([] : List (Form 6)) ++ [F20] = L39 from rfl] at hh
  rw [i15 h, i0 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row11 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L19 + (1 : ℝ) * (CF Γ p).H L43 + (-1 : ℝ) * (CF Γ p).H L44 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F16] ([] : List (Form 6)) [F32]
  rw [show [F16] ++ ([] : List (Form 6)) ++ [F32] = L45 from rfl, show [F16] ++ ([] : List (Form 6)) = L20 from rfl,
    show ([] : List (Form 6)) ++ [F32] = L43 from rfl] at hh
  rw [i16 h, i8 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row12 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L7 + (1 : ℝ) * (CF Γ p).H L46 + (-1 : ℝ) * (CF Γ p).H L47 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F7] ([] : List (Form 6)) [F34]
  rw [show [F7] ++ ([] : List (Form 6)) ++ [F34] = L48 from rfl, show [F7] ++ ([] : List (Form 6)) = L8 from rfl,
    show ([] : List (Form 6)) ++ [F34] = L46 from rfl] at hh
  rw [i17 h, i3 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row13 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L5 + (1 : ℝ) * (CF Γ p).H L49 + (-1 : ℝ) * (CF Γ p).H L51 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F5] ([] : List (Form 6)) [F27]
  rw [show [F5] ++ ([] : List (Form 6)) ++ [F27] = L52 from rfl, show [F5] ++ ([] : List (Form 6)) = L6 from rfl,
    show ([] : List (Form 6)) ++ [F27] = L50 from rfl] at hh
  rw [i19 h, i2 h, i18 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row14 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L5 + (1 : ℝ) * (CF Γ p).H L23 + (-1 : ℝ) * (CF Γ p).H L53 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F5] ([] : List (Form 6)) [F18]
  rw [show [F5] ++ ([] : List (Form 6)) ++ [F18] = L54 from rfl, show [F5] ++ ([] : List (Form 6)) = L6 from rfl,
    show ([] : List (Form 6)) ++ [F18] = L23 from rfl] at hh
  rw [i20 h, i2 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row15 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L17 + (1 : ℝ) * (CF Γ p).H L49 + (-1 : ℝ) * (CF Γ p).H L55 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F14] ([] : List (Form 6)) [F27]
  rw [show [F14] ++ ([] : List (Form 6)) ++ [F27] = L56 from rfl, show [F14] ++ ([] : List (Form 6)) = L18 from rfl,
    show ([] : List (Form 6)) ++ [F27] = L50 from rfl] at hh
  rw [i21 h, i7 h, i18 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row16 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L14 + (1 : ℝ) * (CF Γ p).H L2 + (-1 : ℝ) * (CF Γ p).H L57 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F11] ([] : List (Form 6)) [F2]
  rw [show [F11] ++ ([] : List (Form 6)) ++ [F2] = L58 from rfl, show [F11] ++ ([] : List (Form 6)) = L14 from rfl,
    show ([] : List (Form 6)) ++ [F2] = L2 from rfl] at hh
  rw [i22 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row17 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L5 + (1 : ℝ) * (CF Γ p).H L59 + (-1 : ℝ) * (CF Γ p).H L60 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F5] ([] : List (Form 6)) [F23]
  rw [show [F5] ++ ([] : List (Form 6)) ++ [F23] = L61 from rfl, show [F5] ++ ([] : List (Form 6)) = L6 from rfl,
    show ([] : List (Form 6)) ++ [F23] = L59 from rfl] at hh
  rw [i23 h, i2 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row18 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L49 + (1 : ℝ) * (CF Γ p).H L62 + (-1 : ℝ) * (CF Γ p).H L63 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F27] ([] : List (Form 6)) [F31]
  rw [show [F27] ++ ([] : List (Form 6)) ++ [F31] = L64 from rfl, show [F27] ++ ([] : List (Form 6)) = L50 from rfl,
    show ([] : List (Form 6)) ++ [F31] = L62 from rfl] at hh
  rw [i24 h, i18 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row19 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L2 + (1 : ℝ) * (CF Γ p).H L65 + (-1 : ℝ) * (CF Γ p).H L66 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F2] ([] : List (Form 6)) [F36]
  rw [show [F2] ++ ([] : List (Form 6)) ++ [F36] = L67 from rfl, show [F2] ++ ([] : List (Form 6)) = L2 from rfl,
    show ([] : List (Form 6)) ++ [F36] = L65 from rfl] at hh
  rw [i25 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row20 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L5 + (1 : ℝ) * (CF Γ p).H L68 + (-1 : ℝ) * (CF Γ p).H L69 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F5] ([] : List (Form 6)) [F35]
  rw [show [F5] ++ ([] : List (Form 6)) ++ [F35] = L70 from rfl, show [F5] ++ ([] : List (Form 6)) = L6 from rfl,
    show ([] : List (Form 6)) ++ [F35] = L68 from rfl] at hh
  rw [i26 h, i2 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row21 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L2 + (1 : ℝ) * (CF Γ p).H L72 + (-1 : ℝ) * (CF Γ p).H L73 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F2] ([] : List (Form 6)) [F10]
  rw [show [F2] ++ ([] : List (Form 6)) ++ [F10] = L74 from rfl, show [F2] ++ ([] : List (Form 6)) = L2 from rfl,
    show ([] : List (Form 6)) ++ [F10] = L72 from rfl] at hh
  rw [i27 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row22 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L2 + (1 : ℝ) * (CF Γ p).H L75 + (-1 : ℝ) * (CF Γ p).H L76 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F2] ([] : List (Form 6)) [F12]
  rw [show [F2] ++ ([] : List (Form 6)) ++ [F12] = L77 from rfl, show [F2] ++ ([] : List (Form 6)) = L2 from rfl,
    show ([] : List (Form 6)) ++ [F12] = L75 from rfl] at hh
  rw [i28 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row23 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L5 + (1 : ℝ) * (CF Γ p).H L78 + (-1 : ℝ) * (CF Γ p).H L79 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F5] ([] : List (Form 6)) [F40]
  rw [show [F5] ++ ([] : List (Form 6)) ++ [F40] = L80 from rfl, show [F5] ++ ([] : List (Form 6)) = L6 from rfl,
    show ([] : List (Form 6)) ++ [F40] = L78 from rfl] at hh
  rw [i29 h, i2 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row24 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L49 + (1 : ℝ) * (CF Γ p).H L82 + (-1 : ℝ) * (CF Γ p).H L83 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F27] ([] : List (Form 6)) [F42]
  rw [show [F27] ++ ([] : List (Form 6)) ++ [F42] = L84 from rfl, show [F27] ++ ([] : List (Form 6)) = L50 from rfl,
    show ([] : List (Form 6)) ++ [F42] = L82 from rfl] at hh
  rw [i30 h, i18 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row25 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L49 + (1 : ℝ) * (CF Γ p).H L85 + (-1 : ℝ) * (CF Γ p).H L79 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F27] ([] : List (Form 6)) [F41]
  rw [show [F27] ++ ([] : List (Form 6)) ++ [F41] = L86 from rfl, show [F27] ++ ([] : List (Form 6)) = L50 from rfl,
    show ([] : List (Form 6)) ++ [F41] = L85 from rfl] at hh
  rw [i31 h, i18 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row26 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L17 + (1 : ℝ) * (CF Γ p).H L23 + (-1 : ℝ) * (CF Γ p).H L88 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F14] ([] : List (Form 6)) [F18]
  rw [show [F14] ++ ([] : List (Form 6)) ++ [F18] = L89 from rfl, show [F14] ++ ([] : List (Form 6)) = L18 from rfl,
    show ([] : List (Form 6)) ++ [F18] = L23 from rfl] at hh
  rw [i32 h, i7 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row27 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L14 + (1 : ℝ) * (CF Γ p).H L90 + (-1 : ℝ) * (CF Γ p).H L91 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F11] ([] : List (Form 6)) [F30]
  rw [show [F11] ++ ([] : List (Form 6)) ++ [F30] = L92 from rfl, show [F11] ++ ([] : List (Form 6)) = L14 from rfl,
    show ([] : List (Form 6)) ++ [F30] = L90 from rfl] at hh
  rw [i33 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row28 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L17 + (1 : ℝ) * (CF Γ p).H L93 + (-1 : ℝ) * (CF Γ p).H L69 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F14] ([] : List (Form 6)) [F33]
  rw [show [F14] ++ ([] : List (Form 6)) ++ [F33] = L94 from rfl, show [F14] ++ ([] : List (Form 6)) = L18 from rfl,
    show ([] : List (Form 6)) ++ [F33] = L93 from rfl] at hh
  rw [i34 h, i7 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row29 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L11 + (1 : ℝ) * (CF Γ p).H L96 + (-1 : ℝ) * (CF Γ p).H L97 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F8] ([] : List (Form 6)) [F3]
  rw [show [F8] ++ ([] : List (Form 6)) ++ [F3] = L98 from rfl, show [F8] ++ ([] : List (Form 6)) = L11 from rfl,
    show ([] : List (Form 6)) ++ [F3] = L96 from rfl] at hh
  rw [i35 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row30 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L14 + (1 : ℝ) * (CF Γ p).H L96 + (-1 : ℝ) * (CF Γ p).H L99 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F11] ([] : List (Form 6)) [F3]
  rw [show [F11] ++ ([] : List (Form 6)) ++ [F3] = L100 from rfl, show [F11] ++ ([] : List (Form 6)) = L14 from rfl,
    show ([] : List (Form 6)) ++ [F3] = L96 from rfl] at hh
  rw [i36 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row31 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L90 + (1 : ℝ) * (CF Γ p).H L96 + (-1 : ℝ) * (CF Γ p).H L101 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F30] ([] : List (Form 6)) [F3]
  rw [show [F30] ++ ([] : List (Form 6)) ++ [F3] = L102 from rfl, show [F30] ++ ([] : List (Form 6)) = L90 from rfl,
    show ([] : List (Form 6)) ++ [F3] = L96 from rfl] at hh
  rw [i37 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row32 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L14 + (1 : ℝ) * (CF Γ p).H L103 + (-1 : ℝ) * (CF Γ p).H L104 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F11] ([] : List (Form 6)) [F38]
  rw [show [F11] ++ ([] : List (Form 6)) ++ [F38] = L105 from rfl, show [F11] ++ ([] : List (Form 6)) = L14 from rfl,
    show ([] : List (Form 6)) ++ [F38] = L103 from rfl] at hh
  rw [i38 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row33 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L11 + (1 : ℝ) * (CF Γ p).H L107 + (-1 : ℝ) * (CF Γ p).H L108 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F8] ([] : List (Form 6)) [F37]
  rw [show [F8] ++ ([] : List (Form 6)) ++ [F37] = L109 from rfl, show [F8] ++ ([] : List (Form 6)) = L11 from rfl,
    show ([] : List (Form 6)) ++ [F37] = L107 from rfl] at hh
  rw [i39 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row34 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L23 + (1 : ℝ) * (CF Γ p).H L72 + (-1 : ℝ) * (CF Γ p).H L110 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F18] ([] : List (Form 6)) [F10]
  rw [show [F18] ++ ([] : List (Form 6)) ++ [F10] = L111 from rfl, show [F18] ++ ([] : List (Form 6)) = L23 from rfl,
    show ([] : List (Form 6)) ++ [F10] = L72 from rfl] at hh
  rw [i40 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row35 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L14 + (1 : ℝ) * (CF Γ p).H L72 + (-1 : ℝ) * (CF Γ p).H L112 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F11] ([] : List (Form 6)) [F10]
  rw [show [F11] ++ ([] : List (Form 6)) ++ [F10] = L113 from rfl, show [F11] ++ ([] : List (Form 6)) = L14 from rfl,
    show ([] : List (Form 6)) ++ [F10] = L72 from rfl] at hh
  rw [i41 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row36 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L17 + (1 : ℝ) * (CF Γ p).H L35 + (-1 : ℝ) * (CF Γ p).H L114 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F14] ([] : List (Form 6)) [F19]
  rw [show [F14] ++ ([] : List (Form 6)) ++ [F19] = L115 from rfl, show [F14] ++ ([] : List (Form 6)) = L18 from rfl,
    show ([] : List (Form 6)) ++ [F19] = L35 from rfl] at hh
  rw [i42 h, i7 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row37 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L17 + (1 : ℝ) * (CF Γ p).H L82 + (-1 : ℝ) * (CF Γ p).H L116 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F14] ([] : List (Form 6)) [F42]
  rw [show [F14] ++ ([] : List (Form 6)) ++ [F42] = L117 from rfl, show [F14] ++ ([] : List (Form 6)) = L18 from rfl,
    show ([] : List (Form 6)) ++ [F42] = L82 from rfl] at hh
  rw [i43 h, i7 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row38 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L90 + (1 : ℝ) * (CF Γ p).H L118 + (-1 : ℝ) * (CF Γ p).H L119 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F30] ([] : List (Form 6)) [F39]
  rw [show [F30] ++ ([] : List (Form 6)) ++ [F39] = L120 from rfl, show [F30] ++ ([] : List (Form 6)) = L90 from rfl,
    show ([] : List (Form 6)) ++ [F39] = L118 from rfl] at hh
  rw [i44 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row39 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L62 + (1 : ℝ) * (CF Γ p).H L96 + (-1 : ℝ) * (CF Γ p).H L122 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F31] ([] : List (Form 6)) [F3]
  rw [show [F31] ++ ([] : List (Form 6)) ++ [F3] = L123 from rfl, show [F31] ++ ([] : List (Form 6)) = L62 from rfl,
    show ([] : List (Form 6)) ++ [F3] = L96 from rfl] at hh
  rw [i45 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row40 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L65 + (1 : ℝ) * (CF Γ p).H L96 + (-1 : ℝ) * (CF Γ p).H L125 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F36] ([] : List (Form 6)) [F3]
  rw [show [F36] ++ ([] : List (Form 6)) ++ [F3] = L126 from rfl, show [F36] ++ ([] : List (Form 6)) = L65 from rfl,
    show ([] : List (Form 6)) ++ [F3] = L96 from rfl] at hh
  rw [i46 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row41 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L107 + (1 : ℝ) * (CF Γ p).H L72 + (-1 : ℝ) * (CF Γ p).H L128 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F37] ([] : List (Form 6)) [F10]
  rw [show [F37] ++ ([] : List (Form 6)) ++ [F10] = L129 from rfl, show [F37] ++ ([] : List (Form 6)) = L107 from rfl,
    show ([] : List (Form 6)) ++ [F10] = L72 from rfl] at hh
  rw [i47 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row42 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L75 + (1 : ℝ) * (CF Γ p).H L43 + (-1 : ℝ) * (CF Γ p).H L131 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F12] ([] : List (Form 6)) [F32]
  rw [show [F12] ++ ([] : List (Form 6)) ++ [F32] = L132 from rfl, show [F12] ++ ([] : List (Form 6)) = L75 from rfl,
    show ([] : List (Form 6)) ++ [F32] = L43 from rfl] at hh
  rw [i48 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row43 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L134 + (1 : ℝ) * (CF Γ p).H L136 + (-1 : ℝ) * (CF Γ p).H L138 + (-1 : ℝ) * (CF Γ p).H L0 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F16] L1 [F7]
  rw [show [F16] ++ L1 ++ [F7] = L139 from rfl, show [F16] ++ L1 = L135 from rfl,
    show L1 ++ [F7] = L137 from rfl] at hh
  rw [i51 h, i49 h, i50 h, i0 h] at hh
  linarith

theorem row44 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L134 + (1 : ℝ) * (CF Γ p).H L141 + (-1 : ℝ) * (CF Γ p).H L143 + (-1 : ℝ) * (CF Γ p).H L19 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F1] L20 [F30]
  rw [show [F1] ++ L20 ++ [F30] = L144 from rfl, show [F1] ++ L20 = L140 from rfl,
    show L20 ++ [F30] = L142 from rfl] at hh
  rw [i54 h, i52 h, i53 h, i8 h] at hh
  linarith

theorem row45 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L134 + (1 : ℝ) * (CF Γ p).H L145 + (-1 : ℝ) * (CF Γ p).H L147 + (-1 : ℝ) * (CF Γ p).H L19 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F1] L20 [F37]
  rw [show [F1] ++ L20 ++ [F37] = L148 from rfl, show [F1] ++ L20 = L140 from rfl,
    show L20 ++ [F37] = L146 from rfl] at hh
  rw [i56 h, i52 h, i55 h, i8 h] at hh
  linarith

theorem row46 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L12 + (1 : ℝ) * (CF Γ p).H L60 + (-1 : ℝ) * (CF Γ p).H L29 + (-1 : ℝ) * (CF Γ p).H L28 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F1] L28 [F5]
  rw [show [F1] ++ L28 ++ [F5] = L151 from rfl, show [F1] ++ L28 = L149 from rfl,
    show L28 ++ [F5] = L150 from rfl] at hh
  rw [i59 h, i57 h, i58 h] at hh
  linarith

theorem row47 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L12 + (1 : ℝ) * (CF Γ p).H L21 + (-1 : ℝ) * (CF Γ p).H L29 + (-1 : ℝ) * (CF Γ p).H L72 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F1] L72 [F14]
  rw [show [F1] ++ L72 ++ [F14] = L154 from rfl, show [F1] ++ L72 = L152 from rfl,
    show L72 ++ [F14] = L153 from rfl] at hh
  rw [i62 h, i60 h, i61 h] at hh
  linarith

theorem row48 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L12 + (1 : ℝ) * (CF Γ p).H L155 + (-1 : ℝ) * (CF Γ p).H L157 + (-1 : ℝ) * (CF Γ p).H L72 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F1] L72 [F42]
  rw [show [F1] ++ L72 ++ [F42] = L158 from rfl, show [F1] ++ L72 = L152 from rfl,
    show L72 ++ [F42] = L156 from rfl] at hh
  rw [i64 h, i60 h, i63 h] at hh
  linarith

theorem row49 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L29 + (1 : ℝ) * (CF Γ p).H L36 + (-1 : ℝ) * (CF Γ p).H L161 + (-1 : ℝ) * (CF Γ p).H L134 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F5] L140 [F27]
  rw [show [F5] ++ L140 ++ [F27] = L162 from rfl, show [F5] ++ L140 = L159 from rfl,
    show L140 ++ [F27] = L160 from rfl] at hh
  rw [i67 h, i65 h, i66 h, i52 h] at hh
  linarith

theorem row50 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L29 + (1 : ℝ) * (CF Γ p).H L122 + (-1 : ℝ) * (CF Γ p).H L167 + (-1 : ℝ) * (CF Γ p).H L170 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F16] L171 [F7]
  rw [show [F16] ++ L171 ++ [F7] = L168 from rfl, show [F16] ++ L171 = L163 from rfl,
    show L171 ++ [F7] = L165 from rfl] at hh
  rw [i70 h, i68 h, i69 h, i71 h] at hh
  linarith

theorem row51 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L15 + (1 : ℝ) * (CF Γ p).H L24 + (-1 : ℝ) * (CF Γ p).H L36 + (-1 : ℝ) * (CF Γ p).H L75 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F1] L75 [F18]
  rw [show [F1] ++ L75 ++ [F18] = L175 from rfl, show [F1] ++ L75 = L173 from rfl,
    show L75 ++ [F18] = L174 from rfl] at hh
  rw [i74 h, i72 h, i73 h] at hh
  linarith

theorem row52 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L36 + (1 : ℝ) * (CF Γ p).H L177 + (-1 : ℝ) * (CF Γ p).H L161 + (-1 : ℝ) * (CF Γ p).H L180 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F1] L181 [F14]
  rw [show [F1] ++ L181 ++ [F14] = L179 from rfl, show [F1] ++ L181 = L176 from rfl,
    show L181 ++ [F14] = L178 from rfl] at hh
  rw [i77 h, i75 h, i76 h, i78 h] at hh
  linarith

theorem row53 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L36 + (1 : ℝ) * (CF Γ p).H L183 + (-1 : ℝ) * (CF Γ p).H L161 + (-1 : ℝ) * (CF Γ p).H L186 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F1] L187 [F14]
  rw [show [F1] ++ L187 ++ [F14] = L185 from rfl, show [F1] ++ L187 = L182 from rfl,
    show L187 ++ [F14] = L184 from rfl] at hh
  rw [i81 h, i79 h, i80 h, i82 h] at hh
  linarith

theorem row54 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L136 + (1 : ℝ) * (CF Γ p).H L189 + (-1 : ℝ) * (CF Γ p).H L191 + (-1 : ℝ) * (CF Γ p).H L0 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F7] L1 [F39]
  rw [show [F7] ++ L1 ++ [F39] = L192 from rfl, show [F7] ++ L1 = L188 from rfl,
    show L1 ++ [F39] = L190 from rfl] at hh
  rw [i85 h, i83 h, i84 h, i0 h] at hh
  linarith

theorem row55 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L136 + (1 : ℝ) * (CF Γ p).H L193 + (-1 : ℝ) * (CF Γ p).H L195 + (-1 : ℝ) * (CF Γ p).H L7 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F1] L8 [F11]
  rw [show [F1] ++ L8 ++ [F11] = L196 from rfl, show [F1] ++ L8 = L137 from rfl,
    show L8 ++ [F11] = L194 from rfl] at hh
  rw [i87 h, i50 h, i86 h, i3 h] at hh
  linarith

theorem row56 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L136 + (1 : ℝ) * (CF Γ p).H L198 + (-1 : ℝ) * (CF Γ p).H L191 + (-1 : ℝ) * (CF Γ p).H L62 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F1] L62 [F41]
  rw [show [F1] ++ L62 ++ [F41] = L200 from rfl, show [F1] ++ L62 = L197 from rfl,
    show L62 ++ [F41] = L199 from rfl] at hh
  rw [i90 h, i88 h, i89 h] at hh
  linarith

theorem row57 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L3 + (1 : ℝ) * (CF Γ p).H L9 + (-1 : ℝ) * (CF Γ p).H L122 + (-1 : ℝ) * (CF Γ p).H L96 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F1] L96 [F5]
  rw [show [F1] ++ L96 ++ [F5] = L203 from rfl, show [F1] ++ L96 = L201 from rfl,
    show L96 ++ [F5] = L202 from rfl] at hh
  rw [i93 h, i91 h, i92 h] at hh
  linarith

theorem row58 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L3 + (1 : ℝ) * (CF Γ p).H L57 + (-1 : ℝ) * (CF Γ p).H L204 + (-1 : ℝ) * (CF Γ p).H L2 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F1] L2 [F11]
  rw [show [F1] ++ L2 ++ [F11] = L205 from rfl, show [F1] ++ L2 = L4 from rfl,
    show L2 ++ [F11] = L57 from rfl] at hh
  rw [i94 h, i1 h] at hh
  linarith

theorem row59 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L122 + (1 : ℝ) * (CF Γ p).H L40 + (-1 : ℝ) * (CF Γ p).H L208 + (-1 : ℝ) * (CF Γ p).H L136 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F5] L137 [F27]
  rw [show [F5] ++ L137 ++ [F27] = L209 from rfl, show [F5] ++ L137 = L206 from rfl,
    show L137 ++ [F27] = L207 from rfl] at hh
  rw [i97 h, i95 h, i96 h, i50 h] at hh
  linarith

theorem row60 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L122 + (1 : ℝ) * (CF Γ p).H L131 + (-1 : ℝ) * (CF Γ p).H L214 + (-1 : ℝ) * (CF Γ p).H L170 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F7] L171 [F11]
  rw [show [F7] ++ L171 ++ [F11] = L215 from rfl, show [F7] ++ L171 = L210 from rfl,
    show L171 ++ [F11] = L212 from rfl] at hh
  rw [i100 h, i98 h, i99 h, i71 h] at hh
  linarith

theorem row61 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L40 + (1 : ℝ) * (CF Γ p).H L219 + (-1 : ℝ) * (CF Γ p).H L222 + (-1 : ℝ) * (CF Γ p).H L225 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F7] L226 [F8]
  rw [show [F7] ++ L226 ++ [F8] = L223 from rfl, show [F7] ++ L226 = L217 from rfl,
    show L226 ++ [F8] = L220 from rfl] at hh
  rw [i103 h, i101 h, i102 h, i104 h] at hh
  linarith

theorem row62 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L40 + (1 : ℝ) * (CF Γ p).H L104 + (-1 : ℝ) * (CF Γ p).H L232 + (-1 : ℝ) * (CF Γ p).H L235 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F1] L236 [F16]
  rw [show [F1] ++ L236 ++ [F16] = L233 from rfl, show [F1] ++ L236 = L228 from rfl,
    show L236 ++ [F16] = L230 from rfl] at hh
  rw [i107 h, i105 h, i106 h, i108 h] at hh
  linarith

theorem row63 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L238 + (1 : ℝ) * (CF Γ p).H L240 + (-1 : ℝ) * (CF Γ p).H L242 + (-1 : ℝ) * (CF Γ p).H L107 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F1] L107 [F2]
  rw [show [F1] ++ L107 ++ [F2] = L243 from rfl, show [F1] ++ L107 = L239 from rfl,
    show L107 ++ [F2] = L241 from rfl] at hh
  rw [i111 h, i109 h, i110 h] at hh
  linarith

theorem row64 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L244 + (1 : ℝ) * (CF Γ p).H L246 + (-1 : ℝ) * (CF Γ p).H L247 + (-1 : ℝ) * (CF Γ p).H L85 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F1] L85 [F20]
  rw [show [F1] ++ L85 ++ [F20] = L248 from rfl, show [F1] ++ L85 = L245 from rfl,
    show L85 ++ [F20] = L246 from rfl] at hh
  rw [i113 h, i112 h] at hh
  linarith

theorem row65 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L251 + (1 : ℝ) * (CF Γ p).H L253 + (-1 : ℝ) * (CF Γ p).H L255 + (-1 : ℝ) * (CF Γ p).H L46 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F14] L46 [F27]
  rw [show [F14] ++ L46 ++ [F27] = L256 from rfl, show [F14] ++ L46 = L252 from rfl,
    show L46 ++ [F27] = L254 from rfl] at hh
  rw [i116 h, i114 h, i115 h] at hh
  linarith

theorem row66 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L53 + (1 : ℝ) * (CF Γ p).H L240 + (-1 : ℝ) * (CF Γ p).H L258 + (-1 : ℝ) * (CF Γ p).H L107 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F5] L107 [F2]
  rw [show [F5] ++ L107 ++ [F2] = L259 from rfl, show [F5] ++ L107 = L257 from rfl,
    show L107 ++ [F2] = L241 from rfl] at hh
  rw [i118 h, i117 h, i110 h] at hh
  linarith

theorem row67 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L260 + (1 : ℝ) * (CF Γ p).H L262 + (-1 : ℝ) * (CF Γ p).H L79 + (-1 : ℝ) * (CF Γ p).H L43 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F5] L43 [F27]
  rw [show [F5] ++ L43 ++ [F27] = L264 from rfl, show [F5] ++ L43 = L261 from rfl,
    show L43 ++ [F27] = L263 from rfl] at hh
  rw [i121 h, i119 h, i120 h] at hh
  linarith

theorem row68 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L108 + (1 : ℝ) * (CF Γ p).H L240 + (-1 : ℝ) * (CF Γ p).H L265 + (-1 : ℝ) * (CF Γ p).H L107 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F8] L107 [F2]
  rw [show [F8] ++ L107 ++ [F2] = L266 from rfl, show [F8] ++ L107 = L109 from rfl,
    show L107 ++ [F2] = L241 from rfl] at hh
  rw [i122 h, i39 h, i110 h] at hh
  linarith

theorem row69 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L79 + (1 : ℝ) * (CF Γ p).H L125 + (-1 : ℝ) * (CF Γ p).H L269 + (-1 : ℝ) * (CF Γ p).H L51 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F16] L52 [F7]
  rw [show [F16] ++ L52 ++ [F7] = L270 from rfl, show [F16] ++ L52 = L267 from rfl,
    show L52 ++ [F7] = L268 from rfl] at hh
  rw [i125 h, i123 h, i124 h, i19 h] at hh
  linarith

theorem row70 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L128 + (1 : ℝ) * (CF Γ p).H L255 + (-1 : ℝ) * (CF Γ p).H L273 + (-1 : ℝ) * (CF Γ p).H L55 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F16] L56 [F7]
  rw [show [F16] ++ L56 ++ [F7] = L274 from rfl, show [F16] ++ L56 = L271 from rfl,
    show L56 ++ [F7] = L272 from rfl] at hh
  rw [i128 h, i126 h, i127 h, i21 h] at hh
  linarith

theorem row71 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L79 + (1 : ℝ) * (CF Γ p).H L275 + (-1 : ℝ) * (CF Γ p).H L277 + (-1 : ℝ) * (CF Γ p).H L51 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F16] L52 [F2]
  rw [show [F16] ++ L52 ++ [F2] = L278 from rfl, show [F16] ++ L52 = L267 from rfl,
    show L52 ++ [F2] = L276 from rfl] at hh
  rw [i130 h, i123 h, i129 h, i19 h] at hh
  linarith

theorem row72 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L279 + (1 : ℝ) * (CF Γ p).H L57 + (-1 : ℝ) * (CF Γ p).H L281 + (-1 : ℝ) * (CF Γ p).H L2 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F5] L2 [F11]
  rw [show [F5] ++ L2 ++ [F11] = L282 from rfl, show [F5] ++ L2 = L280 from rfl,
    show L2 ++ [F11] = L57 from rfl] at hh
  rw [i132 h, i131 h] at hh
  linarith

theorem row73 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L279 + (1 : ℝ) * (CF Γ p).H L284 + (-1 : ℝ) * (CF Γ p).H L277 + (-1 : ℝ) * (CF Γ p).H L62 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F5] L62 [F40]
  rw [show [F5] ++ L62 ++ [F40] = L286 from rfl, show [F5] ++ L62 = L283 from rfl,
    show L62 ++ [F40] = L285 from rfl] at hh
  rw [i135 h, i133 h, i134 h] at hh
  linarith

theorem row74 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L60 + (1 : ℝ) * (CF Γ p).H L289 + (-1 : ℝ) * (CF Γ p).H L291 + (-1 : ℝ) * (CF Γ p).H L32 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F5] L32 [F11]
  rw [show [F5] ++ L32 ++ [F11] = L292 from rfl, show [F5] ++ L32 = L288 from rfl,
    show L32 ++ [F11] = L290 from rfl] at hh
  rw [i138 h, i136 h, i137 h] at hh
  linarith

theorem row75 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L293 + (1 : ℝ) * (CF Γ p).H L76 + (-1 : ℝ) * (CF Γ p).H L296 + (-1 : ℝ) * (CF Γ p).H L118 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F5] L118 [F2]
  rw [show [F5] ++ L118 ++ [F2] = L297 from rfl, show [F5] ++ L118 = L294 from rfl,
    show L118 ++ [F2] = L295 from rfl] at hh
  rw [i141 h, i139 h, i140 h] at hh
  linarith

theorem row76 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L293 + (1 : ℝ) * (CF Γ p).H L299 + (-1 : ℝ) * (CF Γ p).H L300 + (-1 : ℝ) * (CF Γ p).H L82 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F5] L82 [F23]
  rw [show [F5] ++ L82 ++ [F23] = L301 from rfl, show [F5] ++ L82 = L298 from rfl,
    show L82 ++ [F23] = L299 from rfl] at hh
  rw [i143 h, i142 h] at hh
  linarith

theorem row77 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L114 + (1 : ℝ) * (CF Γ p).H L262 + (-1 : ℝ) * (CF Γ p).H L177 + (-1 : ℝ) * (CF Γ p).H L78 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F14] L78 [F27]
  rw [show [F14] ++ L78 ++ [F27] = L304 from rfl, show [F14] ++ L78 = L302 from rfl,
    show L78 ++ [F27] = L303 from rfl] at hh
  rw [i146 h, i144 h, i145 h] at hh
  linarith

theorem row78 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L262 + (1 : ℝ) * (CF Γ p).H L110 + (-1 : ℝ) * (CF Γ p).H L219 + (-1 : ℝ) * (CF Γ p).H L78 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F27] L78 [F18]
  rw [show [F27] ++ L78 ++ [F18] = L307 from rfl, show [F27] ++ L78 = L305 from rfl,
    show L78 ++ [F18] = L306 from rfl] at hh
  rw [i149 h, i147 h, i148 h] at hh
  linarith

theorem row79 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L88 + (1 : ℝ) * (CF Γ p).H L309 + (-1 : ℝ) * (CF Γ p).H L183 + (-1 : ℝ) * (CF Γ p).H L65 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F14] L65 [F8]
  rw [show [F14] ++ L65 ++ [F8] = L311 from rfl, show [F14] ++ L65 = L308 from rfl,
    show L65 ++ [F8] = L310 from rfl] at hh
  rw [i152 h, i150 h, i151 h] at hh
  linarith

theorem row80 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L312 + (1 : ℝ) * (CF Γ p).H L309 + (-1 : ℝ) * (CF Γ p).H L315 + (-1 : ℝ) * (CF Γ p).H L65 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F43] L65 [F8]
  rw [show [F43] ++ L65 ++ [F8] = L316 from rfl, show [F43] ++ L65 = L313 from rfl,
    show L65 ++ [F8] = L310 from rfl] at hh
  rw [i154 h, i153 h, i151 h] at hh
  linarith

theorem row81 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L309 + (1 : ℝ) * (CF Γ p).H L66 + (-1 : ℝ) * (CF Γ p).H L320 + (-1 : ℝ) * (CF Γ p).H L65 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F8] L65 [F2]
  rw [show [F8] ++ L65 ++ [F2] = L321 from rfl, show [F8] ++ L65 = L318 from rfl,
    show L65 ++ [F2] = L319 from rfl] at hh
  rw [i157 h, i155 h, i156 h] at hh
  linarith

theorem row82 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L116 + (1 : ℝ) * (CF Γ p).H L322 + (-1 : ℝ) * (CF Γ p).H L324 + (-1 : ℝ) * (CF Γ p).H L82 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F14] L82 [F31]
  rw [show [F14] ++ L82 ++ [F31] = L325 from rfl, show [F14] ++ L82 = L117 from rfl,
    show L82 ++ [F31] = L323 from rfl] at hh
  rw [i159 h, i43 h, i158 h] at hh
  linarith

theorem row83 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L131 + (1 : ℝ) * (CF Γ p).H L191 + (-1 : ℝ) * (CF Γ p).H L214 + (-1 : ℝ) * (CF Γ p).H L244 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F5] L245 [F7]
  rw [show [F5] ++ L245 ++ [F7] = L328 from rfl, show [F5] ++ L245 = L326 from rfl,
    show L245 ++ [F7] = L327 from rfl] at hh
  rw [i162 h, i160 h, i161 h, i112 h] at hh
  linarith

theorem row84 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L161 + (1 : ℝ) * (CF Γ p).H L208 + (-1 : ℝ) * (CF Γ p).H L247 + (-1 : ℝ) * (CF Γ p).H L69 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F16] L335 [F7]
  rw [show [F16] ++ L335 ++ [F7] = L333 from rfl, show [F16] ++ L335 = L329 from rfl,
    show L335 ++ [F7] = L331 from rfl] at hh
  rw [i165 h, i163 h, i164 h, i166 h] at hh
  linarith

theorem row85 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L180 + (1 : ℝ) * (CF Γ p).H L299 + (-1 : ℝ) * (CF Γ p).H L338 + (-1 : ℝ) * (CF Γ p).H L59 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F27] L59 [F42]
  rw [show [F27] ++ L59 ++ [F42] = L339 from rfl, show [F27] ++ L59 = L181 from rfl,
    show L59 ++ [F42] = L337 from rfl] at hh
  rw [i168 h, i78 h, i167 h] at hh
  linarith

theorem row86 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L63 + (1 : ℝ) * (CF Γ p).H L26 + (-1 : ℝ) * (CF Γ p).H L40 + (-1 : ℝ) * (CF Γ p).H L39 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F27] L39 [F18]
  rw [show [F27] ++ L39 ++ [F18] = L342 from rfl, show [F27] ++ L39 = L340 from rfl,
    show L39 ++ [F18] = L341 from rfl] at hh
  rw [i171 h, i169 h, i170 h] at hh
  linarith

theorem row87 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L63 + (1 : ℝ) * (CF Γ p).H L66 + (-1 : ℝ) * (CF Γ p).H L275 + (-1 : ℝ) * (CF Γ p).H L39 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F27] L39 [F2]
  rw [show [F27] ++ L39 ++ [F2] = L344 from rfl, show [F27] ++ L39 = L340 from rfl,
    show L39 ++ [F2] = L343 from rfl] at hh
  rw [i173 h, i169 h, i172 h] at hh
  linarith

theorem row88 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L83 + (1 : ℝ) * (CF Γ p).H L97 + (-1 : ℝ) * (CF Γ p).H L347 + (-1 : ℝ) * (CF Γ p).H L103 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F27] L103 [F8]
  rw [show [F27] ++ L103 ++ [F8] = L348 from rfl, show [F27] ++ L103 = L345 from rfl,
    show L103 ++ [F8] = L346 from rfl] at hh
  rw [i176 h, i174 h, i175 h] at hh
  linarith

theorem row89 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L83 + (1 : ℝ) * (CF Γ p).H L73 + (-1 : ℝ) * (CF Γ p).H L350 + (-1 : ℝ) * (CF Γ p).H L103 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F27] L103 [F2]
  rw [show [F27] ++ L103 ++ [F2] = L351 from rfl, show [F27] ++ L103 = L345 from rfl,
    show L103 ++ [F2] = L349 from rfl] at hh
  rw [i178 h, i174 h, i177 h] at hh
  linarith

theorem row90 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L83 + (1 : ℝ) * (CF Γ p).H L299 + (-1 : ℝ) * (CF Γ p).H L338 + (-1 : ℝ) * (CF Γ p).H L82 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F27] L82 [F23]
  rw [show [F27] ++ L82 ++ [F23] = L352 from rfl, show [F27] ++ L82 = L84 from rfl,
    show L82 ++ [F23] = L299 from rfl] at hh
  rw [i179 h, i30 h] at hh
  linarith

theorem row91 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L24 + (1 : ℝ) * (CF Γ p).H L108 + (-1 : ℝ) * (CF Γ p).H L355 + (-1 : ℝ) * (CF Γ p).H L35 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F18] L35 [F8]
  rw [show [F18] ++ L35 ++ [F8] = L356 from rfl, show [F18] ++ L35 = L353 from rfl,
    show L35 ++ [F8] = L354 from rfl] at hh
  rw [i182 h, i180 h, i181 h] at hh
  linarith

theorem row92 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L355 + (1 : ℝ) * (CF Γ p).H L358 + (-1 : ℝ) * (CF Γ p).H L360 + (-1 : ℝ) * (CF Γ p).H L145 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F5] L146 [F2]
  rw [show [F5] ++ L146 ++ [F2] = L361 from rfl, show [F5] ++ L146 = L357 from rfl,
    show L146 ++ [F2] = L359 from rfl] at hh
  rw [i185 h, i183 h, i184 h, i55 h] at hh
  linarith

theorem row93 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L355 + (1 : ℝ) * (CF Γ p).H L265 + (-1 : ℝ) * (CF Γ p).H L360 + (-1 : ℝ) * (CF Γ p).H L108 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F5] L109 [F2]
  rw [show [F5] ++ L109 ++ [F2] = L363 from rfl, show [F5] ++ L109 = L362 from rfl,
    show L109 ++ [F2] = L266 from rfl] at hh
  rw [i187 h, i186 h, i122 h, i39 h] at hh
  linarith

theorem row94 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L186 + (1 : ℝ) * (CF Γ p).H L365 + (-1 : ℝ) * (CF Γ p).H L232 + (-1 : ℝ) * (CF Γ p).H L59 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F18] L59 [F38]
  rw [show [F18] ++ L59 ++ [F38] = L367 from rfl, show [F18] ++ L59 = L364 from rfl,
    show L59 ++ [F38] = L366 from rfl] at hh
  rw [i190 h, i188 h, i189 h] at hh
  linarith

theorem row95 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L26 + (1 : ℝ) * (CF Γ p).H L370 + (-1 : ℝ) * (CF Γ p).H L372 + (-1 : ℝ) * (CF Γ p).H L39 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F18] L39 [F11]
  rw [show [F18] ++ L39 ++ [F11] = L373 from rfl, show [F18] ++ L39 = L369 from rfl,
    show L39 ++ [F11] = L371 from rfl] at hh
  rw [i193 h, i191 h, i192 h] at hh
  linarith

theorem row96 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L26 + (1 : ℝ) * (CF Γ p).H L66 + (-1 : ℝ) * (CF Γ p).H L312 + (-1 : ℝ) * (CF Γ p).H L39 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F18] L39 [F2]
  rw [show [F18] ++ L39 ++ [F2] = L374 from rfl, show [F18] ++ L39 = L369 from rfl,
    show L39 ++ [F2] = L343 from rfl] at hh
  rw [i194 h, i191 h, i172 h] at hh
  linarith

theorem row97 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L312 + (1 : ℝ) * (CF Γ p).H L377 + (-1 : ℝ) * (CF Γ p).H L380 + (-1 : ℝ) * (CF Γ p).H L383 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F18] L384 [F16]
  rw [show [F18] ++ L384 ++ [F16] = L381 from rfl, show [F18] ++ L384 = L375 from rfl,
    show L384 ++ [F16] = L378 from rfl] at hh
  rw [i197 h, i195 h, i196 h, i198 h] at hh
  linarith

theorem row98 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L386 + (1 : ℝ) * (CF Γ p).H L388 + (-1 : ℝ) * (CF Γ p).H L232 + (-1 : ℝ) * (CF Γ p).H L62 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F18] L62 [F38]
  rw [show [F18] ++ L62 ++ [F38] = L390 from rfl, show [F18] ++ L62 = L387 from rfl,
    show L62 ++ [F38] = L389 from rfl] at hh
  rw [i201 h, i199 h, i200 h] at hh
  linarith

theorem row99 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L141 + (1 : ℝ) * (CF Γ p).H L393 + (-1 : ℝ) * (CF Γ p).H L358 + (-1 : ℝ) * (CF Γ p).H L82 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F16] L82 [F2]
  rw [show [F16] ++ L82 ++ [F2] = L395 from rfl, show [F16] ++ L82 = L392 from rfl,
    show L82 ++ [F2] = L394 from rfl] at hh
  rw [i204 h, i202 h, i203 h] at hh
  linarith

theorem row100 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L141 + (1 : ℝ) * (CF Γ p).H L396 + (-1 : ℝ) * (CF Γ p).H L397 + (-1 : ℝ) * (CF Γ p).H L82 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F16] L82 [F9]
  rw [show [F16] ++ L82 ++ [F9] = L398 from rfl, show [F16] ++ L82 = L392 from rfl,
    show L82 ++ [F9] = L396 from rfl] at hh
  rw [i205 h, i202 h] at hh
  linarith

theorem row101 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L44 + (1 : ℝ) * (CF Γ p).H L101 + (-1 : ℝ) * (CF Γ p).H L402 + (-1 : ℝ) * (CF Γ p).H L93 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F16] L93 [F30]
  rw [show [F16] ++ L93 ++ [F30] = L403 from rfl, show [F16] ++ L93 = L400 from rfl,
    show L93 ++ [F30] = L401 from rfl] at hh
  rw [i208 h, i206 h, i207 h] at hh
  linarith

theorem row102 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L167 + (1 : ℝ) * (CF Γ p).H L273 + (-1 : ℝ) * (CF Γ p).H L247 + (-1 : ℝ) * (CF Γ p).H L377 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F1] L410 [F27]
  rw [show [F1] ++ L410 ++ [F27] = L408 from rfl, show [F1] ++ L410 = L404 from rfl,
    show L410 ++ [F27] = L406 from rfl] at hh
  rw [i211 h, i209 h, i210 h, i212 h] at hh
  linarith

theorem row103 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L167 + (1 : ℝ) * (CF Γ p).H L338 + (-1 : ℝ) * (CF Γ p).H L247 + (-1 : ℝ) * (CF Γ p).H L365 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F22] L366 [F27]
  rw [show [F22] ++ L366 ++ [F27] = L415 from rfl, show [F22] ++ L366 = L412 from rfl,
    show L366 ++ [F27] = L414 from rfl] at hh
  rw [i215 h, i213 h, i214 h, i189 h] at hh
  linarith

theorem row104 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L167 + (1 : ℝ) * (CF Γ p).H L418 + (-1 : ℝ) * (CF Γ p).H L247 + (-1 : ℝ) * (CF Γ p).H L421 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F1] L422 [F27]
  rw [show [F1] ++ L422 ++ [F27] = L420 from rfl, show [F1] ++ L422 = L417 from rfl,
    show L422 ++ [F27] = L419 from rfl] at hh
  rw [i218 h, i216 h, i217 h, i219 h] at hh
  linarith

theorem row105 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L119 + (1 : ℝ) * (CF Γ p).H L424 + (-1 : ℝ) * (CF Γ p).H L269 + (-1 : ℝ) * (CF Γ p).H L293 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F16] L298 [F11]
  rw [show [F16] ++ L298 ++ [F11] = L426 from rfl, show [F16] ++ L298 = L423 from rfl,
    show L298 ++ [F11] = L425 from rfl] at hh
  rw [i222 h, i220 h, i221 h, i142 h] at hh
  linarith

theorem row106 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L269 + (1 : ℝ) * (CF Γ p).H L214 + (-1 : ℝ) * (CF Γ p).H L247 + (-1 : ℝ) * (CF Γ p).H L424 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F27] L430 [F1]
  rw [show [F27] ++ L430 ++ [F1] = L429 from rfl, show [F27] ++ L430 = L427 from rfl,
    show L430 ++ [F1] = L428 from rfl] at hh
  rw [i225 h, i223 h, i224 h, i226 h] at hh
  linarith

theorem row107 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L269 + (1 : ℝ) * (CF Γ p).H L432 + (-1 : ℝ) * (CF Γ p).H L247 + (-1 : ℝ) * (CF Γ p).H L402 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F5] L435 [F1]
  rw [show [F5] ++ L435 ++ [F1] = L434 from rfl, show [F5] ++ L435 = L431 from rfl,
    show L435 ++ [F1] = L433 from rfl] at hh
  rw [i229 h, i227 h, i228 h, i230 h] at hh
  linarith

theorem row108 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L57 + (1 : ℝ) * (CF Γ p).H L91 + (-1 : ℝ) * (CF Γ p).H L436 + (-1 : ℝ) * (CF Γ p).H L14 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F2] L14 [F30]
  rw [show [F2] ++ L14 ++ [F30] = L437 from rfl, show [F2] ++ L14 = L57 from rfl,
    show L14 ++ [F30] = L92 from rfl] at hh
  rw [i231 h, i33 h] at hh
  linarith

theorem row109 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L99 + (1 : ℝ) * (CF Γ p).H L439 + (-1 : ℝ) * (CF Γ p).H L214 + (-1 : ℝ) * (CF Γ p).H L118 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F11] L118 [F31]
  rw [show [F11] ++ L118 ++ [F31] = L440 from rfl, show [F11] ++ L118 = L438 from rfl,
    show L118 ++ [F31] = L439 from rfl] at hh
  rw [i233 h, i232 h] at hh
  linarith

theorem row110 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L112 + (1 : ℝ) * (CF Γ p).H L47 + (-1 : ℝ) * (CF Γ p).H L444 + (-1 : ℝ) * (CF Γ p).H L68 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F11] L68 [F7]
  rw [show [F11] ++ L68 ++ [F7] = L445 from rfl, show [F11] ++ L68 = L442 from rfl,
    show L68 ++ [F7] = L443 from rfl] at hh
  rw [i236 h, i234 h, i235 h] at hh
  linarith

theorem row111 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L446 + (1 : ℝ) * (CF Γ p).H L320 + (-1 : ℝ) * (CF Γ p).H L277 + (-1 : ℝ) * (CF Γ p).H L370 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F27] L370 [F8]
  rw [show [F27] ++ L370 ++ [F8] = L449 from rfl, show [F27] ++ L370 = L447 from rfl,
    show L370 ++ [F8] = L448 from rfl] at hh
  rw [i239 h, i237 h, i238 h] at hh
  linarith

theorem row112 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L388 + (1 : ℝ) * (CF Γ p).H L450 + (-1 : ℝ) * (CF Γ p).H L451 + (-1 : ℝ) * (CF Γ p).H L103 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F31] L103 [F40]
  rw [show [F31] ++ L103 ++ [F40] = L452 from rfl, show [F31] ++ L103 = L389 from rfl,
    show L103 ++ [F40] = L450 from rfl] at hh
  rw [i240 h, i200 h] at hh
  linarith

theorem row113 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L138 + (1 : ℝ) * (CF Γ p).H L454 + (-1 : ℝ) * (CF Γ p).H L456 + (-1 : ℝ) * (CF Γ p).H L388 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F1] L389 [F33]
  rw [show [F1] ++ L389 ++ [F33] = L457 from rfl, show [F1] ++ L389 = L453 from rfl,
    show L389 ++ [F33] = L455 from rfl] at hh
  rw [i243 h, i241 h, i242 h, i200 h] at hh
  linarith

theorem row114 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L143 + (1 : ℝ) * (CF Γ p).H L315 + (-1 : ℝ) * (CF Γ p).H L247 + (-1 : ℝ) * (CF Γ p).H L299 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F1] L337 [F43]
  rw [show [F1] ++ L337 ++ [F43] = L461 from rfl, show [F1] ++ L337 = L458 from rfl,
    show L337 ++ [F43] = L459 from rfl] at hh
  rw [i246 h, i244 h, i245 h, i167 h] at hh
  linarith

theorem row115 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L232 + (1 : ℝ) * (CF Γ p).H L277 + (-1 : ℝ) * (CF Γ p).H L247 + (-1 : ℝ) * (CF Γ p).H L446 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F1] L469 [F5]
  rw [show [F1] ++ L469 ++ [F5] = L467 from rfl, show [F1] ++ L469 = L463 from rfl,
    show L469 ++ [F5] = L465 from rfl] at hh
  rw [i249 h, i247 h, i248 h, i250 h] at hh
  linarith

theorem row116 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L232 + (1 : ℝ) * (CF Γ p).H L421 + (-1 : ℝ) * (CF Γ p).H L247 + (-1 : ℝ) * (CF Γ p).H L388 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F18] L389 [F5]
  rw [show [F18] ++ L389 ++ [F5] = L472 from rfl, show [F18] ++ L389 = L390 from rfl,
    show L389 ++ [F5] = L471 from rfl] at hh
  rw [i252 h, i201 h, i251 h, i200 h] at hh
  linarith

theorem row117 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L232 + (1 : ℝ) * (CF Γ p).H L360 + (-1 : ℝ) * (CF Γ p).H L247 + (-1 : ℝ) * (CF Γ p).H L477 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F1] L478 [F5]
  rw [show [F1] ++ L478 ++ [F5] = L476 from rfl, show [F1] ++ L478 = L474 from rfl,
    show L478 ++ [F5] = L475 from rfl] at hh
  rw [i255 h, i253 h, i254 h, i256 h] at hh
  linarith

theorem row118 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L147 + (1 : ℝ) * (CF Γ p).H L242 + (-1 : ℝ) * (CF Γ p).H L432 + (-1 : ℝ) * (CF Γ p).H L238 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F16] L482 [F2]
  rw [show [F16] ++ L482 ++ [F2] = L481 from rfl, show [F16] ++ L482 = L479 from rfl,
    show L482 ++ [F2] = L480 from rfl] at hh
  rw [i259 h, i257 h, i258 h, i260 h] at hh
  linarith

theorem row119 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L222 + (1 : ℝ) * (CF Γ p).H L277 + (-1 : ℝ) * (CF Γ p).H L247 + (-1 : ℝ) * (CF Γ p).H L486 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F1] L487 [F5]
  rw [show [F1] ++ L487 ++ [F5] = L485 from rfl, show [F1] ++ L487 = L483 from rfl,
    show L487 ++ [F5] = L484 from rfl] at hh
  rw [i263 h, i261 h, i262 h, i264 h] at hh
  linarith

theorem row120 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L222 + (1 : ℝ) * (CF Γ p).H L489 + (-1 : ℝ) * (CF Γ p).H L247 + (-1 : ℝ) * (CF Γ p).H L492 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F1] L493 [F5]
  rw [show [F1] ++ L493 ++ [F5] = L491 from rfl, show [F1] ++ L493 = L488 from rfl,
    show L493 ++ [F5] = L490 from rfl] at hh
  rw [i267 h, i265 h, i266 h, i268 h] at hh
  linarith

theorem row121 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L157 + (1 : ℝ) * (CF Γ p).H L300 + (-1 : ℝ) * (CF Γ p).H L397 + (-1 : ℝ) * (CF Γ p).H L396 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F1] L497 [F5]
  rw [show [F1] ++ L497 ++ [F5] = L496 from rfl, show [F1] ++ L497 = L494 from rfl,
    show L497 ++ [F5] = L495 from rfl] at hh
  rw [i271 h, i269 h, i270 h, i272 h] at hh
  linarith

theorem row122 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L397 + (1 : ℝ) * (CF Γ p).H L204 + (-1 : ℝ) * (CF Γ p).H L247 + (-1 : ℝ) * (CF Γ p).H L189 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F21] L190 [F11]
  rw [show [F21] ++ L190 ++ [F11] = L501 from rfl, show [F21] ++ L190 = L498 from rfl,
    show L190 ++ [F11] = L500 from rfl] at hh
  rw [i275 h, i273 h, i274 h, i84 h] at hh
  linarith

theorem row123 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L397 + (1 : ℝ) * (CF Γ p).H L418 + (-1 : ℝ) * (CF Γ p).H L247 + (-1 : ℝ) * (CF Γ p).H L506 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F1] L507 [F27]
  rw [show [F1] ++ L507 ++ [F27] = L505 from rfl, show [F1] ++ L507 = L503 from rfl,
    show L507 ++ [F27] = L504 from rfl] at hh
  rw [i278 h, i276 h, i277 h, i279 h] at hh
  linarith

theorem row124 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L195 + (1 : ℝ) * (CF Γ p).H L360 + (-1 : ℝ) * (CF Γ p).H L247 + (-1 : ℝ) * (CF Γ p).H L322 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F1] L513 [F21]
  rw [show [F1] ++ L513 ++ [F21] = L511 from rfl, show [F1] ++ L513 = L508 from rfl,
    show L513 ++ [F21] = L509 from rfl] at hh
  rw [i282 h, i280 h, i281 h, i283 h] at hh
  linarith

theorem row125 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L191 + (1 : ℝ) * (CF Γ p).H L296 + (-1 : ℝ) * (CF Γ p).H L214 + (-1 : ℝ) * (CF Γ p).H L439 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F1] L517 [F5]
  rw [show [F1] ++ L517 ++ [F5] = L516 from rfl, show [F1] ++ L517 = L514 from rfl,
    show L517 ++ [F5] = L515 from rfl] at hh
  rw [i286 h, i284 h, i285 h, i287 h] at hh
  linarith

theorem row126 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L291 + (1 : ℝ) * (CF Γ p).H L436 + (-1 : ℝ) * (CF Γ p).H L489 + (-1 : ℝ) * (CF Γ p).H L289 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F5] L521 [F2]
  rw [show [F5] ++ L521 ++ [F2] = L520 from rfl, show [F5] ++ L521 = L518 from rfl,
    show L521 ++ [F2] = L519 from rfl] at hh
  rw [i290 h, i288 h, i289 h, i291 h] at hh
  linarith

theorem row127 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L258 + (1 : ℝ) * (CF Γ p).H L421 + (-1 : ℝ) * (CF Γ p).H L247 + (-1 : ℝ) * (CF Γ p).H L279 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F18] L280 [F38]
  rw [show [F18] ++ L280 ++ [F38] = L523 from rfl, show [F18] ++ L280 = L522 from rfl,
    show L280 ++ [F38] = L422 from rfl] at hh
  rw [i293 h, i292 h, i219 h, i131 h] at hh
  linarith

theorem row128 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L424 + (1 : ℝ) * (CF Γ p).H L372 + (-1 : ℝ) * (CF Γ p).H L526 + (-1 : ℝ) * (CF Γ p).H L193 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F5] L528 [F18]
  rw [show [F5] ++ L528 ++ [F18] = L527 from rfl, show [F5] ++ L528 = L430 from rfl,
    show L528 ++ [F18] = L525 from rfl] at hh
  rw [i295 h, i226 h, i294 h, i296 h] at hh
  linarith

theorem row129 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L281 + (1 : ℝ) * (CF Γ p).H L324 + (-1 : ℝ) * (CF Γ p).H L214 + (-1 : ℝ) * (CF Γ p).H L198 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F5] L199 [F14]
  rw [show [F5] ++ L199 ++ [F14] = L531 from rfl, show [F5] ++ L199 = L529 from rfl,
    show L199 ++ [F14] = L530 from rfl] at hh
  rw [i299 h, i297 h, i298 h, i89 h] at hh
  linarith

theorem row130 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L277 + (1 : ℝ) * (CF Γ p).H L534 + (-1 : ℝ) * (CF Γ p).H L247 + (-1 : ℝ) * (CF Γ p).H L246 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F27] L538 [F18]
  rw [show [F27] ++ L538 ++ [F18] = L536 from rfl, show [F27] ++ L538 = L532 from rfl,
    show L538 ++ [F18] = L535 from rfl] at hh
  rw [i302 h, i300 h, i301 h, i303 h] at hh
  linarith

theorem row131 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L296 + (1 : ℝ) * (CF Γ p).H L350 + (-1 : ℝ) * (CF Γ p).H L418 + (-1 : ℝ) * (CF Γ p).H L393 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F5] L393 [F27]
  rw [show [F5] ++ L393 ++ [F27] = L541 from rfl, show [F5] ++ L393 = L539 from rfl,
    show L393 ++ [F27] = L540 from rfl] at hh
  rw [i306 h, i304 h, i305 h] at hh
  linarith

theorem row132 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L506 + (1 : ℝ) * (CF Γ p).H L444 + (-1 : ℝ) * (CF Γ p).H L247 + (-1 : ℝ) * (CF Γ p).H L155 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F5] L156 [F11]
  rw [show [F5] ++ L156 ++ [F11] = L543 from rfl, show [F5] ++ L156 = L507 from rfl,
    show L156 ++ [F11] = L542 from rfl] at hh
  rw [i308 h, i279 h, i307 h, i63 h] at hh
  linarith

theorem row133 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L486 + (1 : ℝ) * (CF Γ p).H L451 + (-1 : ℝ) * (CF Γ p).H L247 + (-1 : ℝ) * (CF Γ p).H L284 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F27] L285 [F38]
  rw [show [F27] ++ L285 ++ [F38] = L547 from rfl, show [F27] ++ L285 = L545 from rfl,
    show L285 ++ [F38] = L546 from rfl] at hh
  rw [i311 h, i309 h, i310 h, i134 h] at hh
  linarith

theorem row134 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L347 + (1 : ℝ) * (CF Γ p).H L380 + (-1 : ℝ) * (CF Γ p).H L247 + (-1 : ℝ) * (CF Γ p).H L450 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F27] L450 [F43]
  rw [show [F27] ++ L450 ++ [F43] = L552 from rfl, show [F27] ++ L450 = L549 from rfl,
    show L450 ++ [F43] = L550 from rfl] at hh
  rw [i314 h, i312 h, i313 h] at hh
  linarith

theorem row135 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L380 + (1 : ℝ) * (CF Γ p).H L526 + (-1 : ℝ) * (CF Γ p).H L247 + (-1 : ℝ) * (CF Γ p).H L534 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F14] L557 [F5]
  rw [show [F14] ++ L557 ++ [F5] = L556 from rfl, show [F14] ++ L557 = L554 from rfl,
    show L557 ++ [F5] = L555 from rfl] at hh
  rw [i317 h, i315 h, i316 h, i318 h] at hh
  linarith

theorem row136 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L477 + (1 : ℝ) * (CF Γ p).H L492 + (-1 : ℝ) * (CF Γ p).H L247 + (-1 : ℝ) * (CF Γ p).H L386 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F16] L561 [F9]
  rw [show [F16] ++ L561 ++ [F9] = L559 from rfl, show [F16] ++ L561 = L558 from rfl,
    show L561 ++ [F9] = L493 from rfl] at hh
  rw [i320 h, i319 h, i268 h, i321 h] at hh
  linarith

theorem row137 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L477 + (1 : ℝ) * (CF Γ p).H L402 + (-1 : ℝ) * (CF Γ p).H L247 + (-1 : ℝ) * (CF Γ p).H L141 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F18] L142 [F33]
  rw [show [F18] ++ L142 ++ [F33] = L562 from rfl, show [F18] ++ L142 = L478 from rfl,
    show L142 ++ [F33] = L435 from rfl] at hh
  rw [i322 h, i256 h, i230 h, i53 h] at hh
  linarith

theorem row138 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L456 + (1 : ℝ) * (CF Γ p).H L418 + (-1 : ℝ) * (CF Γ p).H L247 + (-1 : ℝ) * (CF Γ p).H L454 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F1] L567 [F5]
  rw [show [F1] ++ L567 ++ [F5] = L566 from rfl, show [F1] ++ L567 = L564 from rfl,
    show L567 ++ [F5] = L565 from rfl] at hh
  rw [i325 h, i323 h, i324 h, i326 h] at hh
  linarith

theorem row139 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    (1 : ℝ) * (CF Γ p).H L225 + (1 : ℝ) * (CF Γ p).H L170 + (-1 : ℝ) * (CF Γ p).H L69 + (-1 : ℝ) * (CF Γ p).H L0 = 0 := by
  have hh : (C1 Γ p).H (L571 ++ L572 ++ L1) + (C1 Γ p).H L1 = (C1 Γ p).H (L571 ++ L1) + (C1 Γ p).H (L572 ++ L1) :=
    Conf.H_copy_ci (src := src0) (V := V0) (hv0 h) (by decide) L571 L572 L571 (by decide) (by decide) (by decide)
      (by decide)
  rw [show L571 ++ L572 ++ L1 = L570 from rfl, show L571 ++ L1 = L569 from rfl, show L572 ++ L1 = L568 from rfl] at hh
  rw [← lift1 h L570 (by decide) (by decide), ← lift1 h L1 (by decide) (by decide), ← lift1 h L569 (by decide) (by decide), ← lift1 h L568 (by decide) (by decide)] at hh
  rw [i329 h, i0 h, i328 h, i327 h] at hh
  linarith

theorem row140 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    (1 : ℝ) * (CF Γ p).H L79 + (1 : ℝ) * (CF Γ p).H L69 + (-1 : ℝ) * (CF Γ p).H L161 + (-1 : ℝ) * (CF Γ p).H L51 = 0 := by
  have hh : (C2 Γ p).H (L576 ++ L577 ++ L52) + (C2 Γ p).H L52 = (C2 Γ p).H (L576 ++ L52) + (C2 Γ p).H (L577 ++ L52) :=
    Conf.H_copy_ci (src := src1) (V := V1) (hv1 h) (by decide) L576 L577 L576 (by decide) (by decide) (by decide)
      (by decide)
  rw [show L576 ++ L577 ++ L52 = L575 from rfl, show L576 ++ L52 = L574 from rfl, show L577 ++ L52 = L573 from rfl] at hh
  rw [← lift2 h L575 (by decide), ← lift2 h L52 (by decide), ← lift2 h L574 (by decide), ← lift2 h L573 (by decide)] at hh
  rw [i332 h, i19 h, i331 h, i330 h] at hh
  linarith

theorem row141 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    (1 : ℝ) * (CF Γ p).H L255 + (1 : ℝ) * (CF Γ p).H L161 + (-1 : ℝ) * (CF Γ p).H L247 + (-1 : ℝ) * (CF Γ p).H L55 = 0 := by
  have hh : (CF Γ p).H (L581 ++ L582 ++ L56) + (CF Γ p).H L56 = (CF Γ p).H (L581 ++ L56) + (CF Γ p).H (L582 ++ L56) :=
    Conf.H_copy_ci (src := src2) (V := V2) (hv2 h) (by decide) L581 L582 L576 (by decide) (by decide) (by decide)
      (by decide)
  rw [show L581 ++ L582 ++ L56 = L580 from rfl, show L581 ++ L56 = L579 from rfl, show L582 ++ L56 = L578 from rfl] at hh
  rw [i335 h, i21 h, i334 h, i333 h] at hh
  linarith

theorem row142 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    (1 : ℝ) * (CF Γ p).H L49 + (-1 : ℝ) * (CF Γ p).H L5 = 0 := by
  have hh : (C1 Γ p).H (L50 ++ ([] : List (Form 6))) = (C1 Γ p).H (L6 ++ ([] : List (Form 6))) :=
    Conf.H_copy_eqlaw (src := src0) (V := V0) (hv0 h) (by decide) L50 ([] : List (Form 6)) L6 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L50 ++ ([] : List (Form 6)) = L50 from rfl, show L6 ++ ([] : List (Form 6)) = L6 from rfl] at hh
  rw [← lift1 h L6 (by decide) (by decide), ← lift1 h L50 (by decide) (by decide)] at hh
  rw [i2 h, i18 h] at hh
  linarith

theorem row143 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    (1 : ℝ) * (CF Γ p).H L23 + (-1 : ℝ) * (CF Γ p).H L17 = 0 := by
  have hh : (C1 Γ p).H (L23 ++ ([] : List (Form 6))) = (C1 Γ p).H (L18 ++ ([] : List (Form 6))) :=
    Conf.H_copy_eqlaw (src := src0) (V := V0) (hv0 h) (by decide) L23 ([] : List (Form 6)) L18 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L23 ++ ([] : List (Form 6)) = L23 from rfl, show L18 ++ ([] : List (Form 6)) = L18 from rfl] at hh
  rw [← lift1 h L18 (by decide) (by decide), ← lift1 h L23 (by decide) (by decide)] at hh
  rw [i7 h] at hh
  linarith

theorem row144 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    (1 : ℝ) * (CF Γ p).H L225 + (-1 : ℝ) * (CF Γ p).H L170 = 0 := by
  have hh : (C1 Γ p).H (L226 ++ ([] : List (Form 6))) = (C1 Γ p).H (L171 ++ ([] : List (Form 6))) :=
    Conf.H_copy_eqlaw (src := src0) (V := V0) (hv0 h) (by decide) L226 ([] : List (Form 6)) L171 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L226 ++ ([] : List (Form 6)) = L226 from rfl, show L171 ++ ([] : List (Form 6)) = L171 from rfl] at hh
  rw [← lift1 h L171 (by decide) (by decide), ← lift1 h L226 (by decide) (by decide)] at hh
  rw [i71 h, i104 h] at hh
  linarith

theorem row145 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    (1 : ℝ) * (CF Γ p).H L19 + (-1 : ℝ) * (CF Γ p).H L0 = 0 := by
  have hh : (C2 Γ p).H (L20 ++ ([] : List (Form 6))) = (C2 Γ p).H (L1 ++ ([] : List (Form 6))) :=
    Conf.H_copy_eqlaw (src := src1) (V := V1) (hv1 h) (by decide) L20 ([] : List (Form 6)) L1 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L20 ++ ([] : List (Form 6)) = L20 from rfl, show L1 ++ ([] : List (Form 6)) = L1 from rfl] at hh
  rw [← lift2 h L1 (by decide), ← lift2 h L20 (by decide)] at hh
  rw [i0 h, i8 h] at hh
  linarith

theorem row146 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    (1 : ℝ) * (CF Γ p).H L11 + (-1 : ℝ) * (CF Γ p).H L17 = 0 := by
  have hh : (C2 Γ p).H (L11 ++ ([] : List (Form 6))) = (C2 Γ p).H (L18 ++ ([] : List (Form 6))) :=
    Conf.H_copy_eqlaw (src := src1) (V := V1) (hv1 h) (by decide) L11 ([] : List (Form 6)) L18 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L11 ++ ([] : List (Form 6)) = L11 from rfl, show L18 ++ ([] : List (Form 6)) = L18 from rfl] at hh
  rw [← lift2 h L18 (by decide), ← lift2 h L11 (by decide)] at hh
  rw [i7 h] at hh
  linarith

theorem row147 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    (1 : ℝ) * (CF Γ p).H L583 + (-1 : ℝ) * (CF Γ p).H L170 = 0 := by
  have hh : (C2 Γ p).H (L584 ++ ([] : List (Form 6))) = (C2 Γ p).H (L171 ++ ([] : List (Form 6))) :=
    Conf.H_copy_eqlaw (src := src1) (V := V1) (hv1 h) (by decide) L584 ([] : List (Form 6)) L171 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L584 ++ ([] : List (Form 6)) = L584 from rfl, show L171 ++ ([] : List (Form 6)) = L171 from rfl] at hh
  rw [← lift2 h L171 (by decide), ← lift2 h L584 (by decide)] at hh
  rw [i71 h, i336 h] at hh
  linarith

theorem row148 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    (1 : ℝ) * (CF Γ p).H L14 + (-1 : ℝ) * (CF Γ p).H L23 = 0 := by
  have hh : (C2 Γ p).H (L14 ++ ([] : List (Form 6))) = (C2 Γ p).H (L23 ++ ([] : List (Form 6))) :=
    Conf.H_copy_eqlaw (src := src1) (V := V1) (hv1 h) (by decide) L14 ([] : List (Form 6)) L23 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L14 ++ ([] : List (Form 6)) = L14 from rfl, show L23 ++ ([] : List (Form 6)) = L23 from rfl] at hh
  rw [← lift2 h L23 (by decide), ← lift2 h L14 (by decide)] at hh
  linarith

theorem row149 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    (1 : ℝ) * (CF Γ p).H L586 + (-1 : ℝ) * (CF Γ p).H L225 = 0 := by
  have hh : (C2 Γ p).H (L587 ++ ([] : List (Form 6))) = (C2 Γ p).H (L226 ++ ([] : List (Form 6))) :=
    Conf.H_copy_eqlaw (src := src1) (V := V1) (hv1 h) (by decide) L587 ([] : List (Form 6)) L226 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L587 ++ ([] : List (Form 6)) = L587 from rfl, show L226 ++ ([] : List (Form 6)) = L226 from rfl] at hh
  rw [← lift2 h L226 (by decide), ← lift2 h L587 (by decide)] at hh
  rw [i104 h, i337 h] at hh
  linarith

end EntropyBounds.GlueZ.Certs.C3BALL
