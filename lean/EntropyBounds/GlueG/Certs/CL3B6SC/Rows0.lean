import EntropyBounds.GlueG.Certs.CL3B6SC.Ids0
import EntropyBounds.GlueG.Certs.CL3B6SC.Ids1
import EntropyBounds.GlueG.Certs.CL3B6SC.Ids2
import EntropyBounds.GlueG.Certs.CL3B6SC.Ids3
import EntropyBounds.GlueG.Certs.CL3B6SC.Ids4
import EntropyBounds.Glue.Certs.CL3B6SC.Lemmas
import EntropyBounds.GlueG.Lemma

set_option linter.unusedVariables false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open Finset

namespace EntropyBounds.GlueG.Certs.CL3B6SC

variable {G : Type} [AddCommGroup G] [DecidableEq G]

open EntropyBounds.Iid EntropyBounds.GlueG SumsDifferences SumsDifferences.NonShannon
open EntropyBounds.Lem

theorem row0 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L2 := by
  have hh := Conf.H_mono (hvF h).nonneg L3 [F44]
  rw [show L3 ++ [F44] = L1 from rfl] at hh
  rw [i0 h, i1 h] at hh
  linarith

theorem row1 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L5 := by
  have hh := Conf.H_mono (hvF h).nonneg L6 [F44]
  rw [show L6 ++ [F44] = L4 from rfl] at hh
  rw [i2 h, i3 h] at hh
  linarith

theorem row2 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L9 := by
  have hh := Conf.H_mono (hvF h).nonneg L10 [F44]
  rw [show L10 ++ [F44] = L7 from rfl] at hh
  rw [i4 h, i5 h] at hh
  linarith

theorem row3 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L11 + (1 : ℝ) * (CF Γ p).H L13 + (-1 : ℝ) * (CF Γ p).H L15 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F15] ([] : List (Form 6)) [F6]
  rw [show [F15] ++ ([] : List (Form 6)) ++ [F6] = L16 from rfl, show [F15] ++ ([] : List (Form 6)) = L12 from rfl,
    show ([] : List (Form 6)) ++ [F6] = L14 from rfl] at hh
  rw [i8 h, i6 h, i7 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row4 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L17 + (1 : ℝ) * (CF Γ p).H L19 + (-1 : ℝ) * (CF Γ p).H L20 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] ([] : List (Form 6)) [F4]
  rw [show [F44] ++ ([] : List (Form 6)) ++ [F4] = L21 from rfl, show [F44] ++ ([] : List (Form 6)) = L18 from rfl,
    show ([] : List (Form 6)) ++ [F4] = L19 from rfl] at hh
  rw [i10 h, i9 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row5 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L22 + (1 : ℝ) * (CF Γ p).H L13 + (-1 : ℝ) * (CF Γ p).H L24 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F29] ([] : List (Form 6)) [F6]
  rw [show [F29] ++ ([] : List (Form 6)) ++ [F6] = L25 from rfl, show [F29] ++ ([] : List (Form 6)) = L23 from rfl,
    show ([] : List (Form 6)) ++ [F6] = L14 from rfl] at hh
  rw [i12 h, i11 h, i7 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row6 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L17 + (1 : ℝ) * (CF Γ p).H L26 + (-1 : ℝ) * (CF Γ p).H L27 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] ([] : List (Form 6)) [F17]
  rw [show [F44] ++ ([] : List (Form 6)) ++ [F17] = L28 from rfl, show [F44] ++ ([] : List (Form 6)) = L18 from rfl,
    show ([] : List (Form 6)) ++ [F17] = L26 from rfl] at hh
  rw [i13 h, i9 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row7 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L17 + (1 : ℝ) * (CF Γ p).H L29 + (-1 : ℝ) * (CF Γ p).H L30 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] ([] : List (Form 6)) [F11]
  rw [show [F44] ++ ([] : List (Form 6)) ++ [F11] = L31 from rfl, show [F44] ++ ([] : List (Form 6)) = L18 from rfl,
    show ([] : List (Form 6)) ++ [F11] = L29 from rfl] at hh
  rw [i14 h, i9 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row8 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L17 + (1 : ℝ) * (CF Γ p).H L32 + (-1 : ℝ) * (CF Γ p).H L33 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] ([] : List (Form 6)) [F3]
  rw [show [F44] ++ ([] : List (Form 6)) ++ [F3] = L34 from rfl, show [F44] ++ ([] : List (Form 6)) = L18 from rfl,
    show ([] : List (Form 6)) ++ [F3] = L32 from rfl] at hh
  rw [i15 h, i9 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row9 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L35 + (1 : ℝ) * (CF Γ p).H L11 + (-1 : ℝ) * (CF Γ p).H L37 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F58] ([] : List (Form 6)) [F15]
  rw [show [F58] ++ ([] : List (Form 6)) ++ [F15] = L38 from rfl, show [F58] ++ ([] : List (Form 6)) = L36 from rfl,
    show ([] : List (Form 6)) ++ [F15] = L12 from rfl] at hh
  rw [i17 h, i16 h, i6 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row10 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L39 + (1 : ℝ) * (CF Γ p).H L11 + (-1 : ℝ) * (CF Γ p).H L40 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F22] ([] : List (Form 6)) [F15]
  rw [show [F22] ++ ([] : List (Form 6)) ++ [F15] = L41 from rfl, show [F22] ++ ([] : List (Form 6)) = L39 from rfl,
    show ([] : List (Form 6)) ++ [F15] = L12 from rfl] at hh
  rw [i18 h, i6 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row11 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L39 + (1 : ℝ) * (CF Γ p).H L13 + (-1 : ℝ) * (CF Γ p).H L42 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F22] ([] : List (Form 6)) [F6]
  rw [show [F22] ++ ([] : List (Form 6)) ++ [F6] = L43 from rfl, show [F22] ++ ([] : List (Form 6)) = L39 from rfl,
    show ([] : List (Form 6)) ++ [F6] = L14 from rfl] at hh
  rw [i19 h, i7 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row12 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L13 + (1 : ℝ) * (CF Γ p).H L44 + (-1 : ℝ) * (CF Γ p).H L45 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F6] ([] : List (Form 6)) [F62]
  rw [show [F6] ++ ([] : List (Form 6)) ++ [F62] = L46 from rfl, show [F6] ++ ([] : List (Form 6)) = L14 from rfl,
    show ([] : List (Form 6)) ++ [F62] = L44 from rfl] at hh
  rw [i20 h, i7 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row13 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L11 + (1 : ℝ) * (CF Γ p).H L47 + (-1 : ℝ) * (CF Γ p).H L48 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F15] ([] : List (Form 6)) [F34]
  rw [show [F15] ++ ([] : List (Form 6)) ++ [F34] = L49 from rfl, show [F15] ++ ([] : List (Form 6)) = L12 from rfl,
    show ([] : List (Form 6)) ++ [F34] = L47 from rfl] at hh
  rw [i21 h, i6 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row14 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L17 + (1 : ℝ) * (CF Γ p).H L51 + (-1 : ℝ) * (CF Γ p).H L48 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] ([] : List (Form 6)) [F57]
  rw [show [F44] ++ ([] : List (Form 6)) ++ [F57] = L52 from rfl, show [F44] ++ ([] : List (Form 6)) = L18 from rfl,
    show ([] : List (Form 6)) ++ [F57] = L51 from rfl] at hh
  rw [i22 h, i9 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row15 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L17 + (1 : ℝ) * (CF Γ p).H L54 + (-1 : ℝ) * (CF Γ p).H L55 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] ([] : List (Form 6)) [F48]
  rw [show [F44] ++ ([] : List (Form 6)) ++ [F48] = L56 from rfl, show [F44] ++ ([] : List (Form 6)) = L18 from rfl,
    show ([] : List (Form 6)) ++ [F48] = L54 from rfl] at hh
  rw [i23 h, i9 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row16 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L13 + (1 : ℝ) * (CF Γ p).H L58 + (-1 : ℝ) * (CF Γ p).H L59 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F6] ([] : List (Form 6)) [F39]
  rw [show [F6] ++ ([] : List (Form 6)) ++ [F39] = L60 from rfl, show [F6] ++ ([] : List (Form 6)) = L14 from rfl,
    show ([] : List (Form 6)) ++ [F39] = L58 from rfl] at hh
  rw [i24 h, i7 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row17 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L17 + (1 : ℝ) * (CF Γ p).H L62 + (-1 : ℝ) * (CF Γ p).H L59 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] ([] : List (Form 6)) [F50]
  rw [show [F44] ++ ([] : List (Form 6)) ++ [F50] = L63 from rfl, show [F44] ++ ([] : List (Form 6)) = L18 from rfl,
    show ([] : List (Form 6)) ++ [F50] = L62 from rfl] at hh
  rw [i25 h, i9 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row18 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L17 + (1 : ℝ) * (CF Γ p).H L65 + (-1 : ℝ) * (CF Γ p).H L66 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] ([] : List (Form 6)) [F41]
  rw [show [F44] ++ ([] : List (Form 6)) ++ [F41] = L67 from rfl, show [F44] ++ ([] : List (Form 6)) = L18 from rfl,
    show ([] : List (Form 6)) ++ [F41] = L65 from rfl] at hh
  rw [i26 h, i9 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row19 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L11 + (1 : ℝ) * (CF Γ p).H L68 + (-1 : ℝ) * (CF Γ p).H L69 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F15] ([] : List (Form 6)) [F33]
  rw [show [F15] ++ ([] : List (Form 6)) ++ [F33] = L70 from rfl, show [F15] ++ ([] : List (Form 6)) = L12 from rfl,
    show ([] : List (Form 6)) ++ [F33] = L68 from rfl] at hh
  rw [i27 h, i6 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row20 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L11 + (1 : ℝ) * (CF Γ p).H L71 + (-1 : ℝ) * (CF Γ p).H L72 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F15] ([] : List (Form 6)) [F24]
  rw [show [F15] ++ ([] : List (Form 6)) ++ [F24] = L73 from rfl, show [F15] ++ ([] : List (Form 6)) = L12 from rfl,
    show ([] : List (Form 6)) ++ [F24] = L71 from rfl] at hh
  rw [i28 h, i6 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row21 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L13 + (1 : ℝ) * (CF Γ p).H L74 + (-1 : ℝ) * (CF Γ p).H L75 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F6] ([] : List (Form 6)) [F64]
  rw [show [F6] ++ ([] : List (Form 6)) ++ [F64] = L76 from rfl, show [F6] ++ ([] : List (Form 6)) = L14 from rfl,
    show ([] : List (Form 6)) ++ [F64] = L74 from rfl] at hh
  rw [i29 h, i7 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row22 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L17 + (1 : ℝ) * (CF Γ p).H L77 + (-1 : ℝ) * (CF Γ p).H L78 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] ([] : List (Form 6)) [F63]
  rw [show [F44] ++ ([] : List (Form 6)) ++ [F63] = L79 from rfl, show [F44] ++ ([] : List (Form 6)) = L18 from rfl,
    show ([] : List (Form 6)) ++ [F63] = L77 from rfl] at hh
  rw [i30 h, i9 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row23 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L11 + (1 : ℝ) * (CF Γ p).H L77 + (-1 : ℝ) * (CF Γ p).H L80 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F15] ([] : List (Form 6)) [F63]
  rw [show [F15] ++ ([] : List (Form 6)) ++ [F63] = L81 from rfl, show [F15] ++ ([] : List (Form 6)) = L12 from rfl,
    show ([] : List (Form 6)) ++ [F63] = L77 from rfl] at hh
  rw [i31 h, i6 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row24 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L17 + (1 : ℝ) * (CF Γ p).H L82 + (-1 : ℝ) * (CF Γ p).H L83 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] ([] : List (Form 6)) [F53]
  rw [show [F44] ++ ([] : List (Form 6)) ++ [F53] = L84 from rfl, show [F44] ++ ([] : List (Form 6)) = L18 from rfl,
    show ([] : List (Form 6)) ++ [F53] = L82 from rfl] at hh
  rw [i32 h, i9 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row25 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L11 + (1 : ℝ) * (CF Γ p).H L85 + (-1 : ℝ) * (CF Γ p).H L55 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F15] ([] : List (Form 6)) [F38]
  rw [show [F15] ++ ([] : List (Form 6)) ++ [F38] = L86 from rfl, show [F15] ++ ([] : List (Form 6)) = L12 from rfl,
    show ([] : List (Form 6)) ++ [F38] = L85 from rfl] at hh
  rw [i33 h, i6 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row26 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L22 + (1 : ℝ) * (CF Γ p).H L88 + (-1 : ℝ) * (CF Γ p).H L90 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F29] ([] : List (Form 6)) [F18]
  rw [show [F29] ++ ([] : List (Form 6)) ++ [F18] = L91 from rfl, show [F29] ++ ([] : List (Form 6)) = L23 from rfl,
    show ([] : List (Form 6)) ++ [F18] = L89 from rfl] at hh
  rw [i35 h, i11 h, i34 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row27 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L22 + (1 : ℝ) * (CF Γ p).H L39 + (-1 : ℝ) * (CF Γ p).H L92 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F29] ([] : List (Form 6)) [F22]
  rw [show [F29] ++ ([] : List (Form 6)) ++ [F22] = L93 from rfl, show [F29] ++ ([] : List (Form 6)) = L23 from rfl,
    show ([] : List (Form 6)) ++ [F22] = L39 from rfl] at hh
  rw [i36 h, i11 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row28 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L35 + (1 : ℝ) * (CF Γ p).H L88 + (-1 : ℝ) * (CF Γ p).H L94 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F58] ([] : List (Form 6)) [F18]
  rw [show [F58] ++ ([] : List (Form 6)) ++ [F18] = L95 from rfl, show [F58] ++ ([] : List (Form 6)) = L36 from rfl,
    show ([] : List (Form 6)) ++ [F18] = L89 from rfl] at hh
  rw [i37 h, i16 h, i34 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row29 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L26 + (1 : ℝ) * (CF Γ p).H L19 + (-1 : ℝ) * (CF Γ p).H L96 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F17] ([] : List (Form 6)) [F4]
  rw [show [F17] ++ ([] : List (Form 6)) ++ [F4] = L97 from rfl, show [F17] ++ ([] : List (Form 6)) = L26 from rfl,
    show ([] : List (Form 6)) ++ [F4] = L19 from rfl] at hh
  rw [i38 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row30 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L29 + (1 : ℝ) * (CF Γ p).H L19 + (-1 : ℝ) * (CF Γ p).H L98 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F11] ([] : List (Form 6)) [F4]
  rw [show [F11] ++ ([] : List (Form 6)) ++ [F4] = L99 from rfl, show [F11] ++ ([] : List (Form 6)) = L29 from rfl,
    show ([] : List (Form 6)) ++ [F4] = L19 from rfl] at hh
  rw [i39 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row31 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L22 + (1 : ℝ) * (CF Γ p).H L100 + (-1 : ℝ) * (CF Γ p).H L101 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F29] ([] : List (Form 6)) [F42]
  rw [show [F29] ++ ([] : List (Form 6)) ++ [F42] = L102 from rfl, show [F29] ++ ([] : List (Form 6)) = L23 from rfl,
    show ([] : List (Form 6)) ++ [F42] = L100 from rfl] at hh
  rw [i40 h, i11 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row32 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L88 + (1 : ℝ) * (CF Γ p).H L103 + (-1 : ℝ) * (CF Γ p).H L104 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F18] ([] : List (Form 6)) [F43]
  rw [show [F18] ++ ([] : List (Form 6)) ++ [F43] = L105 from rfl, show [F18] ++ ([] : List (Form 6)) = L89 from rfl,
    show ([] : List (Form 6)) ++ [F43] = L103 from rfl] at hh
  rw [i41 h, i34 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row33 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L19 + (1 : ℝ) * (CF Γ p).H L106 + (-1 : ℝ) * (CF Γ p).H L107 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F4] ([] : List (Form 6)) [F25]
  rw [show [F4] ++ ([] : List (Form 6)) ++ [F25] = L108 from rfl, show [F4] ++ ([] : List (Form 6)) = L19 from rfl,
    show ([] : List (Form 6)) ++ [F25] = L106 from rfl] at hh
  rw [i42 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row34 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L19 + (1 : ℝ) * (CF Γ p).H L109 + (-1 : ℝ) * (CF Γ p).H L110 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F4] ([] : List (Form 6)) [F14]
  rw [show [F4] ++ ([] : List (Form 6)) ++ [F14] = L111 from rfl, show [F4] ++ ([] : List (Form 6)) = L19 from rfl,
    show ([] : List (Form 6)) ++ [F14] = L109 from rfl] at hh
  rw [i43 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row35 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L19 + (1 : ℝ) * (CF Γ p).H L112 + (-1 : ℝ) * (CF Γ p).H L113 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F4] ([] : List (Form 6)) [F60]
  rw [show [F4] ++ ([] : List (Form 6)) ++ [F60] = L114 from rfl, show [F4] ++ ([] : List (Form 6)) = L19 from rfl,
    show ([] : List (Form 6)) ++ [F60] = L112 from rfl] at hh
  rw [i44 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row36 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L19 + (1 : ℝ) * (CF Γ p).H L115 + (-1 : ℝ) * (CF Γ p).H L116 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F4] ([] : List (Form 6)) [F52]
  rw [show [F4] ++ ([] : List (Form 6)) ++ [F52] = L117 from rfl, show [F4] ++ ([] : List (Form 6)) = L19 from rfl,
    show ([] : List (Form 6)) ++ [F52] = L115 from rfl] at hh
  rw [i45 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row37 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L19 + (1 : ℝ) * (CF Γ p).H L118 + (-1 : ℝ) * (CF Γ p).H L119 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F4] ([] : List (Form 6)) [F51]
  rw [show [F4] ++ ([] : List (Form 6)) ++ [F51] = L119 from rfl, show [F4] ++ ([] : List (Form 6)) = L19 from rfl,
    show ([] : List (Form 6)) ++ [F51] = L118 from rfl] at hh
  rw [Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row38 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L22 + (1 : ℝ) * (CF Γ p).H L65 + (-1 : ℝ) * (CF Γ p).H L120 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F29] ([] : List (Form 6)) [F41]
  rw [show [F29] ++ ([] : List (Form 6)) ++ [F41] = L121 from rfl, show [F29] ++ ([] : List (Form 6)) = L23 from rfl,
    show ([] : List (Form 6)) ++ [F41] = L65 from rfl] at hh
  rw [i46 h, i11 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row39 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L19 + (1 : ℝ) * (CF Γ p).H L122 + (-1 : ℝ) * (CF Γ p).H L123 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F4] ([] : List (Form 6)) [F46]
  rw [show [F4] ++ ([] : List (Form 6)) ++ [F46] = L124 from rfl, show [F4] ++ ([] : List (Form 6)) = L19 from rfl,
    show ([] : List (Form 6)) ++ [F46] = L122 from rfl] at hh
  rw [i47 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row40 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L22 + (1 : ℝ) * (CF Γ p).H L126 + (-1 : ℝ) * (CF Γ p).H L127 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F29] ([] : List (Form 6)) [F27]
  rw [show [F29] ++ ([] : List (Form 6)) ++ [F27] = L128 from rfl, show [F29] ++ ([] : List (Form 6)) = L23 from rfl,
    show ([] : List (Form 6)) ++ [F27] = L126 from rfl] at hh
  rw [i48 h, i11 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row41 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L88 + (1 : ℝ) * (CF Γ p).H L130 + (-1 : ℝ) * (CF Γ p).H L131 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F18] ([] : List (Form 6)) [F19]
  rw [show [F18] ++ ([] : List (Form 6)) ++ [F19] = L132 from rfl, show [F18] ++ ([] : List (Form 6)) = L89 from rfl,
    show ([] : List (Form 6)) ++ [F19] = L130 from rfl] at hh
  rw [i49 h, i34 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row42 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L22 + (1 : ℝ) * (CF Γ p).H L133 + (-1 : ℝ) * (CF Γ p).H L134 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F29] ([] : List (Form 6)) [F54]
  rw [show [F29] ++ ([] : List (Form 6)) ++ [F54] = L135 from rfl, show [F29] ++ ([] : List (Form 6)) = L23 from rfl,
    show ([] : List (Form 6)) ++ [F54] = L133 from rfl] at hh
  rw [i50 h, i11 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row43 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L22 + (1 : ℝ) * (CF Γ p).H L136 + (-1 : ℝ) * (CF Γ p).H L137 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F29] ([] : List (Form 6)) [F59]
  rw [show [F29] ++ ([] : List (Form 6)) ++ [F59] = L138 from rfl, show [F29] ++ ([] : List (Form 6)) = L23 from rfl,
    show ([] : List (Form 6)) ++ [F59] = L136 from rfl] at hh
  rw [i51 h, i11 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row44 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L88 + (1 : ℝ) * (CF Γ p).H L82 + (-1 : ℝ) * (CF Γ p).H L139 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F18] ([] : List (Form 6)) [F53]
  rw [show [F18] ++ ([] : List (Form 6)) ++ [F53] = L140 from rfl, show [F18] ++ ([] : List (Form 6)) = L89 from rfl,
    show ([] : List (Form 6)) ++ [F53] = L82 from rfl] at hh
  rw [i52 h, i34 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row45 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L19 + (1 : ℝ) * (CF Γ p).H L85 + (-1 : ℝ) * (CF Γ p).H L141 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F4] ([] : List (Form 6)) [F38]
  rw [show [F4] ++ ([] : List (Form 6)) ++ [F38] = L142 from rfl, show [F4] ++ ([] : List (Form 6)) = L19 from rfl,
    show ([] : List (Form 6)) ++ [F38] = L85 from rfl] at hh
  rw [i53 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row46 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L35 + (1 : ℝ) * (CF Γ p).H L39 + (-1 : ℝ) * (CF Γ p).H L143 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F58] ([] : List (Form 6)) [F22]
  rw [show [F58] ++ ([] : List (Form 6)) ++ [F22] = L144 from rfl, show [F58] ++ ([] : List (Form 6)) = L36 from rfl,
    show ([] : List (Form 6)) ++ [F22] = L39 from rfl] at hh
  rw [i54 h, i16 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row47 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L26 + (1 : ℝ) * (CF Γ p).H L32 + (-1 : ℝ) * (CF Γ p).H L145 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F17] ([] : List (Form 6)) [F3]
  rw [show [F17] ++ ([] : List (Form 6)) ++ [F3] = L146 from rfl, show [F17] ++ ([] : List (Form 6)) = L26 from rfl,
    show ([] : List (Form 6)) ++ [F3] = L32 from rfl] at hh
  rw [i55 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row48 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L29 + (1 : ℝ) * (CF Γ p).H L32 + (-1 : ℝ) * (CF Γ p).H L147 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F11] ([] : List (Form 6)) [F3]
  rw [show [F11] ++ ([] : List (Form 6)) ++ [F3] = L148 from rfl, show [F11] ++ ([] : List (Form 6)) = L29 from rfl,
    show ([] : List (Form 6)) ++ [F3] = L32 from rfl] at hh
  rw [i56 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row49 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L32 + (1 : ℝ) * (CF Γ p).H L100 + (-1 : ℝ) * (CF Γ p).H L149 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F3] ([] : List (Form 6)) [F42]
  rw [show [F3] ++ ([] : List (Form 6)) ++ [F42] = L150 from rfl, show [F3] ++ ([] : List (Form 6)) = L32 from rfl,
    show ([] : List (Form 6)) ++ [F42] = L100 from rfl] at hh
  rw [i57 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row50 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L35 + (1 : ℝ) * (CF Γ p).H L151 + (-1 : ℝ) * (CF Γ p).H L152 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F58] ([] : List (Form 6)) [F31]
  rw [show [F58] ++ ([] : List (Form 6)) ++ [F31] = L153 from rfl, show [F58] ++ ([] : List (Form 6)) = L36 from rfl,
    show ([] : List (Form 6)) ++ [F31] = L151 from rfl] at hh
  rw [i58 h, i16 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row51 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L39 + (1 : ℝ) * (CF Γ p).H L155 + (-1 : ℝ) * (CF Γ p).H L156 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F22] ([] : List (Form 6)) [F28]
  rw [show [F22] ++ ([] : List (Form 6)) ++ [F28] = L157 from rfl, show [F22] ++ ([] : List (Form 6)) = L39 from rfl,
    show ([] : List (Form 6)) ++ [F28] = L155 from rfl] at hh
  rw [i59 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row52 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L26 + (1 : ℝ) * (CF Γ p).H L155 + (-1 : ℝ) * (CF Γ p).H L158 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F17] ([] : List (Form 6)) [F28]
  rw [show [F17] ++ ([] : List (Form 6)) ++ [F28] = L159 from rfl, show [F17] ++ ([] : List (Form 6)) = L26 from rfl,
    show ([] : List (Form 6)) ++ [F28] = L155 from rfl] at hh
  rw [i60 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row53 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L29 + (1 : ℝ) * (CF Γ p).H L155 + (-1 : ℝ) * (CF Γ p).H L160 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F11] ([] : List (Form 6)) [F28]
  rw [show [F11] ++ ([] : List (Form 6)) ++ [F28] = L161 from rfl, show [F11] ++ ([] : List (Form 6)) = L29 from rfl,
    show ([] : List (Form 6)) ++ [F28] = L155 from rfl] at hh
  rw [i61 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row54 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L32 + (1 : ℝ) * (CF Γ p).H L155 + (-1 : ℝ) * (CF Γ p).H L162 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F3] ([] : List (Form 6)) [F28]
  rw [show [F3] ++ ([] : List (Form 6)) ++ [F28] = L163 from rfl, show [F3] ++ ([] : List (Form 6)) = L32 from rfl,
    show ([] : List (Form 6)) ++ [F28] = L155 from rfl] at hh
  rw [i62 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row55 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L29 + (1 : ℝ) * (CF Γ p).H L164 + (-1 : ℝ) * (CF Γ p).H L165 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F11] ([] : List (Form 6)) [F16]
  rw [show [F11] ++ ([] : List (Form 6)) ++ [F16] = L166 from rfl, show [F11] ++ ([] : List (Form 6)) = L29 from rfl,
    show ([] : List (Form 6)) ++ [F16] = L164 from rfl] at hh
  rw [i63 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row56 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L39 + (1 : ℝ) * (CF Γ p).H L112 + (-1 : ℝ) * (CF Γ p).H L168 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F22] ([] : List (Form 6)) [F60]
  rw [show [F22] ++ ([] : List (Form 6)) ++ [F60] = L169 from rfl, show [F22] ++ ([] : List (Form 6)) = L39 from rfl,
    show ([] : List (Form 6)) ++ [F60] = L112 from rfl] at hh
  rw [i64 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row57 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L32 + (1 : ℝ) * (CF Γ p).H L115 + (-1 : ℝ) * (CF Γ p).H L170 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F3] ([] : List (Form 6)) [F52]
  rw [show [F3] ++ ([] : List (Form 6)) ++ [F52] = L171 from rfl, show [F3] ++ ([] : List (Form 6)) = L32 from rfl,
    show ([] : List (Form 6)) ++ [F52] = L115 from rfl] at hh
  rw [i65 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row58 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L29 + (1 : ℝ) * (CF Γ p).H L65 + (-1 : ℝ) * (CF Γ p).H L172 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F11] ([] : List (Form 6)) [F41]
  rw [show [F11] ++ ([] : List (Form 6)) ++ [F41] = L173 from rfl, show [F11] ++ ([] : List (Form 6)) = L29 from rfl,
    show ([] : List (Form 6)) ++ [F41] = L65 from rfl] at hh
  rw [i66 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row59 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L35 + (1 : ℝ) * (CF Γ p).H L68 + (-1 : ℝ) * (CF Γ p).H L174 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F58] ([] : List (Form 6)) [F33]
  rw [show [F58] ++ ([] : List (Form 6)) ++ [F33] = L175 from rfl, show [F58] ++ ([] : List (Form 6)) = L36 from rfl,
    show ([] : List (Form 6)) ++ [F33] = L68 from rfl] at hh
  rw [i67 h, i16 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row60 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L39 + (1 : ℝ) * (CF Γ p).H L176 + (-1 : ℝ) * (CF Γ p).H L177 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F22] ([] : List (Form 6)) [F30]
  rw [show [F22] ++ ([] : List (Form 6)) ++ [F30] = L178 from rfl, show [F22] ++ ([] : List (Form 6)) = L39 from rfl,
    show ([] : List (Form 6)) ++ [F30] = L176 from rfl] at hh
  rw [i68 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row61 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L35 + (1 : ℝ) * (CF Γ p).H L179 + (-1 : ℝ) * (CF Γ p).H L180 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F58] ([] : List (Form 6)) [F61]
  rw [show [F58] ++ ([] : List (Form 6)) ++ [F61] = L181 from rfl, show [F58] ++ ([] : List (Form 6)) = L36 from rfl,
    show ([] : List (Form 6)) ++ [F61] = L179 from rfl] at hh
  rw [i69 h, i16 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row62 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L39 + (1 : ℝ) * (CF Γ p).H L183 + (-1 : ℝ) * (CF Γ p).H L184 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F22] ([] : List (Form 6)) [F56]
  rw [show [F22] ++ ([] : List (Form 6)) ++ [F56] = L185 from rfl, show [F22] ++ ([] : List (Form 6)) = L39 from rfl,
    show ([] : List (Form 6)) ++ [F56] = L183 from rfl] at hh
  rw [i70 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row63 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L32 + (1 : ℝ) * (CF Γ p).H L186 + (-1 : ℝ) * (CF Γ p).H L187 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F3] ([] : List (Form 6)) [F23]
  rw [show [F3] ++ ([] : List (Form 6)) ++ [F23] = L188 from rfl, show [F3] ++ ([] : List (Form 6)) = L32 from rfl,
    show ([] : List (Form 6)) ++ [F23] = L186 from rfl] at hh
  rw [i71 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row64 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L26 + (1 : ℝ) * (CF Γ p).H L77 + (-1 : ℝ) * (CF Γ p).H L190 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F17] ([] : List (Form 6)) [F63]
  rw [show [F17] ++ ([] : List (Form 6)) ++ [F63] = L191 from rfl, show [F17] ++ ([] : List (Form 6)) = L26 from rfl,
    show ([] : List (Form 6)) ++ [F63] = L77 from rfl] at hh
  rw [i72 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row65 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L32 + (1 : ℝ) * (CF Γ p).H L77 + (-1 : ℝ) * (CF Γ p).H L192 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F3] ([] : List (Form 6)) [F63]
  rw [show [F3] ++ ([] : List (Form 6)) ++ [F63] = L192 from rfl, show [F3] ++ ([] : List (Form 6)) = L32 from rfl,
    show ([] : List (Form 6)) ++ [F63] = L77 from rfl] at hh
  rw [Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row66 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L26 + (1 : ℝ) * (CF Γ p).H L82 + (-1 : ℝ) * (CF Γ p).H L193 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F17] ([] : List (Form 6)) [F53]
  rw [show [F17] ++ ([] : List (Form 6)) ++ [F53] = L193 from rfl, show [F17] ++ ([] : List (Form 6)) = L26 from rfl,
    show ([] : List (Form 6)) ++ [F53] = L82 from rfl] at hh
  rw [Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row67 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L26 + (1 : ℝ) * (CF Γ p).H L194 + (-1 : ℝ) * (CF Γ p).H L195 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F17] ([] : List (Form 6)) [F32]
  rw [show [F17] ++ ([] : List (Form 6)) ++ [F32] = L196 from rfl, show [F17] ++ ([] : List (Form 6)) = L26 from rfl,
    show ([] : List (Form 6)) ++ [F32] = L194 from rfl] at hh
  rw [i73 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row68 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L198 + (1 : ℝ) * (CF Γ p).H L200 + (-1 : ℝ) * (CF Γ p).H L202 + (-1 : ℝ) * (CF Γ p).H L11 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F18] L12 [F4]
  rw [show [F18] ++ L12 ++ [F4] = L203 from rfl, show [F18] ++ L12 = L199 from rfl,
    show L12 ++ [F4] = L201 from rfl] at hh
  rw [i76 h, i74 h, i75 h, i6 h] at hh
  linarith

theorem row69 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L198 + (1 : ℝ) * (CF Γ p).H L204 + (-1 : ℝ) * (CF Γ p).H L206 + (-1 : ℝ) * (CF Γ p).H L11 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F18] L12 [F43]
  rw [show [F18] ++ L12 ++ [F43] = L207 from rfl, show [F18] ++ L12 = L199 from rfl,
    show L12 ++ [F43] = L205 from rfl] at hh
  rw [i78 h, i74 h, i77 h, i6 h] at hh
  linarith

theorem row70 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L208 + (1 : ℝ) * (CF Γ p).H L210 + (-1 : ℝ) * (CF Γ p).H L212 + (-1 : ℝ) * (CF Γ p).H L13 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F18] L14 [F42]
  rw [show [F18] ++ L14 ++ [F42] = L213 from rfl, show [F18] ++ L14 = L209 from rfl,
    show L14 ++ [F42] = L211 from rfl] at hh
  rw [i81 h, i79 h, i80 h, i7 h] at hh
  linarith

theorem row71 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L103 + (1 : ℝ) * (CF Γ p).H L155 + (-1 : ℝ) * (CF Γ p).H L214 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F43] ([] : List (Form 6)) [F28]
  rw [show [F43] ++ ([] : List (Form 6)) ++ [F28] = L215 from rfl, show [F43] ++ ([] : List (Form 6)) = L103 from rfl,
    show ([] : List (Form 6)) ++ [F28] = L155 from rfl] at hh
  rw [i82 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row72 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L106 + (1 : ℝ) * (CF Γ p).H L155 + (-1 : ℝ) * (CF Γ p).H L217 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F25] ([] : List (Form 6)) [F28]
  rw [show [F25] ++ ([] : List (Form 6)) ++ [F28] = L218 from rfl, show [F25] ++ ([] : List (Form 6)) = L106 from rfl,
    show ([] : List (Form 6)) ++ [F28] = L155 from rfl] at hh
  rw [i83 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row73 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L155 + (1 : ℝ) * (CF Γ p).H L109 + (-1 : ℝ) * (CF Γ p).H L220 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F28] ([] : List (Form 6)) [F14]
  rw [show [F28] ++ ([] : List (Form 6)) ++ [F14] = L221 from rfl, show [F28] ++ ([] : List (Form 6)) = L155 from rfl,
    show ([] : List (Form 6)) ++ [F14] = L109 from rfl] at hh
  rw [i84 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row74 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L155 + (1 : ℝ) * (CF Γ p).H L223 + (-1 : ℝ) * (CF Γ p).H L224 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F28] ([] : List (Form 6)) [F26]
  rw [show [F28] ++ ([] : List (Form 6)) ++ [F26] = L225 from rfl, show [F28] ++ ([] : List (Form 6)) = L155 from rfl,
    show ([] : List (Form 6)) ++ [F26] = L223 from rfl] at hh
  rw [i85 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row75 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L44 + (1 : ℝ) * (CF Γ p).H L112 + (-1 : ℝ) * (CF Γ p).H L227 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F62] ([] : List (Form 6)) [F60]
  rw [show [F62] ++ ([] : List (Form 6)) ++ [F60] = L228 from rfl, show [F62] ++ ([] : List (Form 6)) = L44 from rfl,
    show ([] : List (Form 6)) ++ [F60] = L112 from rfl] at hh
  rw [i86 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row76 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L44 + (1 : ℝ) * (CF Γ p).H L115 + (-1 : ℝ) * (CF Γ p).H L230 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F62] ([] : List (Form 6)) [F52]
  rw [show [F62] ++ ([] : List (Form 6)) ++ [F52] = L231 from rfl, show [F62] ++ ([] : List (Form 6)) = L44 from rfl,
    show ([] : List (Form 6)) ++ [F52] = L115 from rfl] at hh
  rw [i87 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row77 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L112 + (1 : ℝ) * (CF Γ p).H L77 + (-1 : ℝ) * (CF Γ p).H L233 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F60] ([] : List (Form 6)) [F63]
  rw [show [F60] ++ ([] : List (Form 6)) ++ [F63] = L234 from rfl, show [F60] ++ ([] : List (Form 6)) = L112 from rfl,
    show ([] : List (Form 6)) ++ [F63] = L77 from rfl] at hh
  rw [i88 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row78 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L65 + (1 : ℝ) * (CF Γ p).H L176 + (-1 : ℝ) * (CF Γ p).H L236 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F41] ([] : List (Form 6)) [F30]
  rw [show [F41] ++ ([] : List (Form 6)) ++ [F30] = L237 from rfl, show [F41] ++ ([] : List (Form 6)) = L65 from rfl,
    show ([] : List (Form 6)) ++ [F30] = L176 from rfl] at hh
  rw [i89 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row79 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L239 + (1 : ℝ) * (CF Γ p).H L241 + (-1 : ℝ) * (CF Γ p).H L243 + (-1 : ℝ) * (CF Γ p).H L11 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L12 [F3]
  rw [show [F44] ++ L12 ++ [F3] = L244 from rfl, show [F44] ++ L12 = L240 from rfl,
    show L12 ++ [F3] = L242 from rfl] at hh
  rw [i92 h, i90 h, i91 h, i6 h] at hh
  linarith

theorem row80 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L239 + (1 : ℝ) * (CF Γ p).H L246 + (-1 : ℝ) * (CF Γ p).H L248 + (-1 : ℝ) * (CF Γ p).H L100 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L100 [F4]
  rw [show [F44] ++ L100 ++ [F4] = L249 from rfl, show [F44] ++ L100 = L245 from rfl,
    show L100 ++ [F4] = L247 from rfl] at hh
  rw [i95 h, i93 h, i94 h] at hh
  linarith

theorem row81 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L27 + (1 : ℝ) * (CF Γ p).H L37 + (-1 : ℝ) * (CF Γ p).H L48 + (-1 : ℝ) * (CF Γ p).H L112 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L112 [F58]
  rw [show [F44] ++ L112 ++ [F58] = L252 from rfl, show [F44] ++ L112 = L250 from rfl,
    show L112 ++ [F58] = L251 from rfl] at hh
  rw [i98 h, i96 h, i97 h] at hh
  linarith

theorem row82 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L27 + (1 : ℝ) * (CF Γ p).H L254 + (-1 : ℝ) * (CF Γ p).H L256 + (-1 : ℝ) * (CF Γ p).H L47 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L47 [F22]
  rw [show [F44] ++ L47 ++ [F22] = L257 from rfl, show [F44] ++ L47 = L253 from rfl,
    show L47 ++ [F22] = L255 from rfl] at hh
  rw [i101 h, i99 h, i100 h] at hh
  linarith

theorem row83 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L27 + (1 : ℝ) * (CF Γ p).H L258 + (-1 : ℝ) * (CF Γ p).H L260 + (-1 : ℝ) * (CF Γ p).H L112 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L112 [F19]
  rw [show [F44] ++ L112 ++ [F19] = L261 from rfl, show [F44] ++ L112 = L250 from rfl,
    show L112 ++ [F19] = L259 from rfl] at hh
  rw [i103 h, i96 h, i102 h] at hh
  linarith

theorem row84 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L48 + (1 : ℝ) * (CF Γ p).H L55 + (-1 : ℝ) * (CF Γ p).H L264 + (-1 : ℝ) * (CF Γ p).H L239 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F29] L240 [F18]
  rw [show [F29] ++ L240 ++ [F18] = L265 from rfl, show [F29] ++ L240 = L262 from rfl,
    show L240 ++ [F18] = L263 from rfl] at hh
  rw [i106 h, i104 h, i105 h, i90 h] at hh
  linarith

theorem row85 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L48 + (1 : ℝ) * (CF Γ p).H L214 + (-1 : ℝ) * (CF Γ p).H L270 + (-1 : ℝ) * (CF Γ p).H L273 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F15] L274 [F6]
  rw [show [F15] ++ L274 ++ [F6] = L271 from rfl, show [F15] ++ L274 = L266 from rfl,
    show L274 ++ [F6] = L268 from rfl] at hh
  rw [i109 h, i107 h, i108 h, i110 h] at hh
  linarith

theorem row86 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L30 + (1 : ℝ) * (CF Γ p).H L174 + (-1 : ℝ) * (CF Γ p).H L278 + (-1 : ℝ) * (CF Γ p).H L85 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L85 [F58]
  rw [show [F44] ++ L85 ++ [F58] = L279 from rfl, show [F44] ++ L85 = L276 from rfl,
    show L85 ++ [F58] = L277 from rfl] at hh
  rw [i113 h, i111 h, i112 h] at hh
  linarith

theorem row87 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L30 + (1 : ℝ) * (CF Γ p).H L40 + (-1 : ℝ) * (CF Γ p).H L55 + (-1 : ℝ) * (CF Γ p).H L115 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L115 [F22]
  rw [show [F44] ++ L115 ++ [F22] = L282 from rfl, show [F44] ++ L115 = L280 from rfl,
    show L115 ++ [F22] = L281 from rfl] at hh
  rw [i116 h, i114 h, i115 h] at hh
  linarith

theorem row88 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L30 + (1 : ℝ) * (CF Γ p).H L141 + (-1 : ℝ) * (CF Γ p).H L284 + (-1 : ℝ) * (CF Γ p).H L85 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L85 [F4]
  rw [show [F44] ++ L85 ++ [F4] = L285 from rfl, show [F44] ++ L85 = L276 from rfl,
    show L85 ++ [F4] = L283 from rfl] at hh
  rw [i118 h, i111 h, i117 h] at hh
  linarith

theorem row89 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L30 + (1 : ℝ) * (CF Γ p).H L286 + (-1 : ℝ) * (CF Γ p).H L288 + (-1 : ℝ) * (CF Γ p).H L115 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L115 [F24]
  rw [show [F44] ++ L115 ++ [F24] = L289 from rfl, show [F44] ++ L115 = L280 from rfl,
    show L115 ++ [F24] = L287 from rfl] at hh
  rw [i120 h, i114 h, i119 h] at hh
  linarith

theorem row90 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L290 + (1 : ℝ) * (CF Γ p).H L292 + (-1 : ℝ) * (CF Γ p).H L294 + (-1 : ℝ) * (CF Γ p).H L103 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L103 [F17]
  rw [show [F44] ++ L103 ++ [F17] = L295 from rfl, show [F44] ++ L103 = L291 from rfl,
    show L103 ++ [F17] = L293 from rfl] at hh
  rw [i123 h, i121 h, i122 h] at hh
  linarith

theorem row91 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L290 + (1 : ℝ) * (CF Γ p).H L297 + (-1 : ℝ) * (CF Γ p).H L299 + (-1 : ℝ) * (CF Γ p).H L13 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L14 [F11]
  rw [show [F44] ++ L14 ++ [F11] = L300 from rfl, show [F44] ++ L14 = L296 from rfl,
    show L14 ++ [F11] = L298 from rfl] at hh
  rw [i126 h, i124 h, i125 h, i7 h] at hh
  linarith

theorem row92 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L290 + (1 : ℝ) * (CF Γ p).H L301 + (-1 : ℝ) * (CF Γ p).H L302 + (-1 : ℝ) * (CF Γ p).H L103 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L103 [F48]
  rw [show [F44] ++ L103 ++ [F48] = L303 from rfl, show [F44] ++ L103 = L291 from rfl,
    show L103 ++ [F48] = L301 from rfl] at hh
  rw [i127 h, i121 h] at hh
  linarith

theorem row93 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L20 + (1 : ℝ) * (CF Γ p).H L24 + (-1 : ℝ) * (CF Γ p).H L214 + (-1 : ℝ) * (CF Γ p).H L155 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L155 [F29]
  rw [show [F44] ++ L155 ++ [F29] = L307 from rfl, show [F44] ++ L155 = L305 from rfl,
    show L155 ++ [F29] = L306 from rfl] at hh
  rw [i130 h, i128 h, i129 h] at hh
  linarith

theorem row94 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L214 + (1 : ℝ) * (CF Γ p).H L59 + (-1 : ℝ) * (CF Γ p).H L310 + (-1 : ℝ) * (CF Γ p).H L290 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F29] L296 [F18]
  rw [show [F29] ++ L296 ++ [F18] = L311 from rfl, show [F29] ++ L296 = L308 from rfl,
    show L296 ++ [F18] = L309 from rfl] at hh
  rw [i133 h, i131 h, i132 h, i124 h] at hh
  linarith

theorem row95 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L214 + (1 : ℝ) * (CF Γ p).H L314 + (-1 : ℝ) * (CF Γ p).H L317 + (-1 : ℝ) * (CF Γ p).H L320 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L321 [F11]
  rw [show [F44] ++ L321 ++ [F11] = L318 from rfl, show [F44] ++ L321 = L312 from rfl,
    show L321 ++ [F11] = L315 from rfl] at hh
  rw [i136 h, i134 h, i135 h, i137 h] at hh
  linarith

theorem row96 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L33 + (1 : ℝ) * (CF Γ p).H L134 + (-1 : ℝ) * (CF Γ p).H L325 + (-1 : ℝ) * (CF Γ p).H L58 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L58 [F29]
  rw [show [F44] ++ L58 ++ [F29] = L326 from rfl, show [F44] ++ L58 = L323 from rfl,
    show L58 ++ [F29] = L324 from rfl] at hh
  rw [i140 h, i138 h, i139 h] at hh
  linarith

theorem row97 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L33 + (1 : ℝ) * (CF Γ p).H L119 + (-1 : ℝ) * (CF Γ p).H L329 + (-1 : ℝ) * (CF Γ p).H L118 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L118 [F4]
  rw [show [F44] ++ L118 ++ [F4] = L330 from rfl, show [F44] ++ L118 = L327 from rfl,
    show L118 ++ [F4] = L328 from rfl] at hh
  rw [i143 h, i141 h, i142 h] at hh
  linarith

theorem row98 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L59 + (1 : ℝ) * (CF Γ p).H L332 + (-1 : ℝ) * (CF Γ p).H L334 + (-1 : ℝ) * (CF Γ p).H L42 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L43 [F17]
  rw [show [F44] ++ L43 ++ [F17] = L335 from rfl, show [F44] ++ L43 = L331 from rfl,
    show L43 ++ [F17] = L333 from rfl] at hh
  rw [i146 h, i144 h, i145 h, i19 h] at hh
  linarith

theorem row99 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L66 + (1 : ℝ) * (CF Γ p).H L96 + (-1 : ℝ) * (CF Γ p).H L337 + (-1 : ℝ) * (CF Γ p).H L65 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L65 [F17]
  rw [show [F44] ++ L65 ++ [F17] = L338 from rfl, show [F44] ++ L65 = L67 from rfl,
    show L65 ++ [F17] = L336 from rfl] at hh
  rw [i148 h, i26 h, i147 h] at hh
  linarith

theorem row100 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L339 + (1 : ℝ) * (CF Γ p).H L341 + (-1 : ℝ) * (CF Γ p).H L260 + (-1 : ℝ) * (CF Γ p).H L71 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L71 [F17]
  rw [show [F44] ++ L71 ++ [F17] = L343 from rfl, show [F44] ++ L71 = L340 from rfl,
    show L71 ++ [F17] = L342 from rfl] at hh
  rw [i151 h, i149 h, i150 h] at hh
  linarith

theorem row101 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L344 + (1 : ℝ) * (CF Γ p).H L346 + (-1 : ℝ) * (CF Γ p).H L348 + (-1 : ℝ) * (CF Γ p).H L136 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L136 [F3]
  rw [show [F44] ++ L136 ++ [F3] = L349 from rfl, show [F44] ++ L136 = L345 from rfl,
    show L136 ++ [F3] = L347 from rfl] at hh
  rw [i154 h, i152 h, i153 h] at hh
  linarith

theorem row102 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L83 + (1 : ℝ) * (CF Γ p).H L72 + (-1 : ℝ) * (CF Γ p).H L352 + (-1 : ℝ) * (CF Γ p).H L186 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L186 [F15]
  rw [show [F44] ++ L186 ++ [F15] = L353 from rfl, show [F44] ++ L186 = L350 from rfl,
    show L186 ++ [F15] = L351 from rfl] at hh
  rw [i157 h, i155 h, i156 h] at hh
  linarith

theorem row103 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L78 + (1 : ℝ) * (CF Γ p).H L355 + (-1 : ℝ) * (CF Γ p).H L357 + (-1 : ℝ) * (CF Γ p).H L194 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L194 [F18]
  rw [show [F44] ++ L194 ++ [F18] = L358 from rfl, show [F44] ++ L194 = L354 from rfl,
    show L194 ++ [F18] = L356 from rfl] at hh
  rw [i160 h, i158 h, i159 h] at hh
  linarith

theorem row104 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L359 + (1 : ℝ) * (CF Γ p).H L361 + (-1 : ℝ) * (CF Γ p).H L180 + (-1 : ℝ) * (CF Γ p).H L133 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F58] L133 [F18]
  rw [show [F58] ++ L133 ++ [F18] = L363 from rfl, show [F58] ++ L133 = L360 from rfl,
    show L133 ++ [F18] = L362 from rfl] at hh
  rw [i163 h, i161 h, i162 h] at hh
  linarith

theorem row105 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L361 + (1 : ℝ) * (CF Γ p).H L156 + (-1 : ℝ) * (CF Γ p).H L366 + (-1 : ℝ) * (CF Γ p).H L179 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F18] L179 [F22]
  rw [show [F18] ++ L179 ++ [F22] = L367 from rfl, show [F18] ++ L179 = L364 from rfl,
    show L179 ++ [F22] = L365 from rfl] at hh
  rw [i166 h, i164 h, i165 h] at hh
  linarith

theorem row106 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L92 + (1 : ℝ) * (CF Γ p).H L369 + (-1 : ℝ) * (CF Γ p).H L371 + (-1 : ℝ) * (CF Γ p).H L44 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F29] L44 [F4]
  rw [show [F29] ++ L44 ++ [F4] = L372 from rfl, show [F29] ++ L44 = L368 from rfl,
    show L44 ++ [F4] = L370 from rfl] at hh
  rw [i169 h, i167 h, i168 h] at hh
  linarith

theorem row107 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L373 + (1 : ℝ) * (CF Γ p).H L375 + (-1 : ℝ) * (CF Γ p).H L127 + (-1 : ℝ) * (CF Γ p).H L68 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F29] L68 [F18]
  rw [show [F29] ++ L68 ++ [F18] = L377 from rfl, show [F29] ++ L68 = L374 from rfl,
    show L68 ++ [F18] = L376 from rfl] at hh
  rw [i172 h, i170 h, i171 h] at hh
  linarith

theorem row108 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L127 + (1 : ℝ) * (CF Γ p).H L310 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L90 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F15] L91 [F5]
  rw [show [F15] ++ L91 ++ [F5] = L381 from rfl, show [F15] ++ L91 = L378 from rfl,
    show L91 ++ [F5] = L379 from rfl] at hh
  rw [i175 h, i173 h, i174 h, i35 h] at hh
  linarith

theorem row109 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L383 + (1 : ℝ) * (CF Γ p).H L385 + (-1 : ℝ) * (CF Γ p).H L371 + (-1 : ℝ) * (CF Γ p).H L103 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F29] L103 [F22]
  rw [show [F29] ++ L103 ++ [F22] = L387 from rfl, show [F29] ++ L103 = L384 from rfl,
    show L103 ++ [F22] = L386 from rfl] at hh
  rw [i178 h, i176 h, i177 h] at hh
  linarith

theorem row110 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L383 + (1 : ℝ) * (CF Γ p).H L388 + (-1 : ℝ) * (CF Γ p).H L390 + (-1 : ℝ) * (CF Γ p).H L103 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F29] L103 [F11]
  rw [show [F29] ++ L103 ++ [F11] = L391 from rfl, show [F29] ++ L103 = L384 from rfl,
    show L103 ++ [F11] = L389 from rfl] at hh
  rw [i180 h, i176 h, i179 h] at hh
  linarith

theorem row111 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L392 + (1 : ℝ) * (CF Γ p).H L394 + (-1 : ℝ) * (CF Γ p).H L371 + (-1 : ℝ) * (CF Γ p).H L71 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F29] L71 [F22]
  rw [show [F29] ++ L71 ++ [F22] = L396 from rfl, show [F29] ++ L71 = L393 from rfl,
    show L71 ++ [F22] = L395 from rfl] at hh
  rw [i183 h, i181 h, i182 h] at hh
  linarith

theorem row112 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L392 + (1 : ℝ) * (CF Γ p).H L397 + (-1 : ℝ) * (CF Γ p).H L399 + (-1 : ℝ) * (CF Γ p).H L71 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F29] L71 [F42]
  rw [show [F29] ++ L71 ++ [F42] = L400 from rfl, show [F29] ++ L71 = L393 from rfl,
    show L71 ++ [F42] = L398 from rfl] at hh
  rw [i185 h, i181 h, i184 h] at hh
  linarith

theorem row113 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L101 + (1 : ℝ) * (CF Γ p).H L110 + (-1 : ℝ) * (CF Γ p).H L403 + (-1 : ℝ) * (CF Γ p).H L51 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F29] L51 [F4]
  rw [show [F29] ++ L51 ++ [F4] = L404 from rfl, show [F29] ++ L51 = L401 from rfl,
    show L51 ++ [F4] = L402 from rfl] at hh
  rw [i188 h, i186 h, i187 h] at hh
  linarith

theorem row114 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L120 + (1 : ℝ) * (CF Γ p).H L139 + (-1 : ℝ) * (CF Γ p).H L407 + (-1 : ℝ) * (CF Γ p).H L183 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F29] L183 [F18]
  rw [show [F29] ++ L183 ++ [F18] = L408 from rfl, show [F29] ++ L183 = L405 from rfl,
    show L183 ++ [F18] = L406 from rfl] at hh
  rw [i191 h, i189 h, i190 h] at hh
  linarith

theorem row115 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L120 + (1 : ℝ) * (CF Γ p).H L409 + (-1 : ℝ) * (CF Γ p).H L411 + (-1 : ℝ) * (CF Γ p).H L183 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F29] L183 [F11]
  rw [show [F29] ++ L183 ++ [F11] = L412 from rfl, show [F29] ++ L183 = L405 from rfl,
    show L183 ++ [F11] = L410 from rfl] at hh
  rw [i193 h, i189 h, i192 h] at hh
  linarith

theorem row116 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L120 + (1 : ℝ) * (CF Γ p).H L413 + (-1 : ℝ) * (CF Γ p).H L414 + (-1 : ℝ) * (CF Γ p).H L183 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F29] L183 [F63]
  rw [show [F29] ++ L183 ++ [F63] = L415 from rfl, show [F29] ++ L183 = L405 from rfl,
    show L183 ++ [F63] = L413 from rfl] at hh
  rw [i194 h, i189 h] at hh
  linarith

theorem row117 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L137 + (1 : ℝ) * (CF Γ p).H L170 + (-1 : ℝ) * (CF Γ p).H L418 + (-1 : ℝ) * (CF Γ p).H L122 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F29] L122 [F3]
  rw [show [F29] ++ L122 ++ [F3] = L419 from rfl, show [F29] ++ L122 = L416 from rfl,
    show L122 ++ [F3] = L417 from rfl] at hh
  rw [i197 h, i195 h, i196 h] at hh
  linarith

theorem row118 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L420 + (1 : ℝ) * (CF Γ p).H L184 + (-1 : ℝ) * (CF Γ p).H L423 + (-1 : ℝ) * (CF Γ p).H L186 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F29] L186 [F22]
  rw [show [F29] ++ L186 ++ [F22] = L424 from rfl, show [F29] ++ L186 = L421 from rfl,
    show L186 ++ [F22] = L422 from rfl] at hh
  rw [i200 h, i198 h, i199 h] at hh
  linarith

theorem row119 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L420 + (1 : ℝ) * (CF Γ p).H L116 + (-1 : ℝ) * (CF Γ p).H L426 + (-1 : ℝ) * (CF Γ p).H L186 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F29] L186 [F4]
  rw [show [F29] ++ L186 ++ [F4] = L427 from rfl, show [F29] ++ L186 = L421 from rfl,
    show L186 ++ [F4] = L425 from rfl] at hh
  rw [i202 h, i198 h, i201 h] at hh
  linarith

theorem row120 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L420 + (1 : ℝ) * (CF Γ p).H L429 + (-1 : ℝ) * (CF Γ p).H L431 + (-1 : ℝ) * (CF Γ p).H L130 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F29] L130 [F42]
  rw [show [F29] ++ L130 ++ [F42] = L432 from rfl, show [F29] ++ L130 = L428 from rfl,
    show L130 ++ [F42] = L430 from rfl] at hh
  rw [i205 h, i203 h, i204 h] at hh
  linarith

theorem row121 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L433 + (1 : ℝ) * (CF Γ p).H L98 + (-1 : ℝ) * (CF Γ p).H L390 + (-1 : ℝ) * (CF Γ p).H L82 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F29] L82 [F11]
  rw [show [F29] ++ L82 ++ [F11] = L436 from rfl, show [F29] ++ L82 = L434 from rfl,
    show L82 ++ [F11] = L435 from rfl] at hh
  rw [i208 h, i206 h, i207 h] at hh
  linarith

theorem row122 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L375 + (1 : ℝ) * (CF Γ p).H L168 + (-1 : ℝ) * (CF Γ p).H L256 + (-1 : ℝ) * (CF Γ p).H L126 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F18] L126 [F22]
  rw [show [F18] ++ L126 ++ [F22] = L439 from rfl, show [F18] ++ L126 = L437 from rfl,
    show L126 ++ [F22] = L438 from rfl] at hh
  rw [i211 h, i209 h, i210 h] at hh
  linarith

theorem row123 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L375 + (1 : ℝ) * (CF Γ p).H L441 + (-1 : ℝ) * (CF Γ p).H L443 + (-1 : ℝ) * (CF Γ p).H L68 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F18] L68 [F4]
  rw [show [F18] ++ L68 ++ [F4] = L444 from rfl, show [F18] ++ L68 = L440 from rfl,
    show L68 ++ [F4] = L442 from rfl] at hh
  rw [i214 h, i212 h, i213 h] at hh
  linarith

theorem row124 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L143 + (1 : ℝ) * (CF Γ p).H L446 + (-1 : ℝ) * (CF Γ p).H L448 + (-1 : ℝ) * (CF Γ p).H L106 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F58] L106 [F17]
  rw [show [F58] ++ L106 ++ [F17] = L449 from rfl, show [F58] ++ L106 = L445 from rfl,
    show L106 ++ [F17] = L447 from rfl] at hh
  rw [i217 h, i215 h, i216 h] at hh
  linarith

theorem row125 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L359 + (1 : ℝ) * (CF Γ p).H L450 + (-1 : ℝ) * (CF Γ p).H L452 + (-1 : ℝ) * (CF Γ p).H L133 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F58] L133 [F41]
  rw [show [F58] ++ L133 ++ [F41] = L453 from rfl, show [F58] ++ L133 = L360 from rfl,
    show L133 ++ [F41] = L451 from rfl] at hh
  rw [i219 h, i161 h, i218 h] at hh
  linarith

theorem row126 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L454 + (1 : ℝ) * (CF Γ p).H L456 + (-1 : ℝ) * (CF Γ p).H L448 + (-1 : ℝ) * (CF Γ p).H L100 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F58] L100 [F22]
  rw [show [F58] ++ L100 ++ [F22] = L458 from rfl, show [F58] ++ L100 = L455 from rfl,
    show L100 ++ [F22] = L457 from rfl] at hh
  rw [i222 h, i220 h, i221 h] at hh
  linarith

theorem row127 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L454 + (1 : ℝ) * (CF Γ p).H L149 + (-1 : ℝ) * (CF Γ p).H L460 + (-1 : ℝ) * (CF Γ p).H L100 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F58] L100 [F3]
  rw [show [F58] ++ L100 ++ [F3] = L461 from rfl, show [F58] ++ L100 = L455 from rfl,
    show L100 ++ [F3] = L459 from rfl] at hh
  rw [i224 h, i220 h, i223 h] at hh
  linarith

theorem row128 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L454 + (1 : ℝ) * (CF Γ p).H L462 + (-1 : ℝ) * (CF Γ p).H L464 + (-1 : ℝ) * (CF Γ p).H L100 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F58] L100 [F43]
  rw [show [F58] ++ L100 ++ [F43] = L465 from rfl, show [F58] ++ L100 = L455 from rfl,
    show L100 ++ [F43] = L463 from rfl] at hh
  rw [i226 h, i220 h, i225 h] at hh
  linarith

theorem row129 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L466 + (1 : ℝ) * (CF Γ p).H L468 + (-1 : ℝ) * (CF Γ p).H L448 + (-1 : ℝ) * (CF Γ p).H L74 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F58] L74 [F22]
  rw [show [F58] ++ L74 ++ [F22] = L470 from rfl, show [F58] ++ L74 = L467 from rfl,
    show L74 ++ [F22] = L469 from rfl] at hh
  rw [i229 h, i227 h, i228 h] at hh
  linarith

theorem row130 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L264 + (1 : ℝ) * (CF Γ p).H L473 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L227 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L478 [F6]
  rw [show [F44] ++ L478 ++ [F6] = L476 from rfl, show [F44] ++ L478 = L471 from rfl,
    show L478 ++ [F6] = L474 from rfl] at hh
  rw [i232 h, i230 h, i231 h, i233 h] at hh
  linarith

theorem row131 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L264 + (1 : ℝ) * (CF Γ p).H L481 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L484 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L485 [F6]
  rw [show [F44] ++ L485 ++ [F6] = L483 from rfl, show [F44] ++ L485 = L480 from rfl,
    show L485 ++ [F6] = L482 from rfl] at hh
  rw [i236 h, i234 h, i235 h, i237 h] at hh
  linarith

theorem row132 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L264 + (1 : ℝ) * (CF Γ p).H L487 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L490 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L491 [F4]
  rw [show [F44] ++ L491 ++ [F4] = L489 from rfl, show [F44] ++ L491 = L486 from rfl,
    show L491 ++ [F4] = L488 from rfl] at hh
  rw [i240 h, i238 h, i239 h, i241 h] at hh
  linarith

theorem row133 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L310 + (1 : ℝ) * (CF Γ p).H L494 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L217 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L499 [F15]
  rw [show [F44] ++ L499 ++ [F15] = L497 from rfl, show [F44] ++ L499 = L492 from rfl,
    show L499 ++ [F15] = L495 from rfl] at hh
  rw [i244 h, i242 h, i243 h, i245 h] at hh
  linarith

theorem row134 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L310 + (1 : ℝ) * (CF Γ p).H L502 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L505 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F44] L506 [F15]
  rw [show [F44] ++ L506 ++ [F15] = L504 from rfl, show [F44] ++ L506 = L501 from rfl,
    show L506 ++ [F15] = L503 from rfl] at hh
  rw [i248 h, i246 h, i247 h, i249 h] at hh
  linarith

theorem row135 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L310 + (1 : ℝ) * (CF Γ p).H L508 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L511 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F29] L512 [F17]
  rw [show [F29] ++ L512 ++ [F17] = L510 from rfl, show [F29] ++ L512 = L507 from rfl,
    show L512 ++ [F17] = L509 from rfl] at hh
  rw [i252 h, i250 h, i251 h, i253 h] at hh
  linarith

theorem row136 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L104 + (1 : ℝ) * (CF Γ p).H L190 + (-1 : ℝ) * (CF Γ p).H L515 + (-1 : ℝ) * (CF Γ p).H L62 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F18] L62 [F17]
  rw [show [F18] ++ L62 ++ [F17] = L516 from rfl, show [F18] ++ L62 = L513 from rfl,
    show L62 ++ [F17] = L514 from rfl] at hh
  rw [i256 h, i254 h, i255 h] at hh
  linarith

theorem row137 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L517 + (1 : ℝ) * (CF Γ p).H L519 + (-1 : ℝ) * (CF Γ p).H L310 + (-1 : ℝ) * (CF Γ p).H L71 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F18] L71 [F43]
  rw [show [F18] ++ L71 ++ [F43] = L521 from rfl, show [F18] ++ L71 = L518 from rfl,
    show L71 ++ [F43] = L520 from rfl] at hh
  rw [i259 h, i257 h, i258 h] at hh
  linarith

theorem row138 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L131 + (1 : ℝ) * (CF Γ p).H L15 + (-1 : ℝ) * (CF Γ p).H L165 + (-1 : ℝ) * (CF Γ p).H L164 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F18] L164 [F15]
  rw [show [F18] ++ L164 ++ [F15] = L525 from rfl, show [F18] ++ L164 = L523 from rfl,
    show L164 ++ [F15] = L524 from rfl] at hh
  rw [i262 h, i260 h, i261 h] at hh
  linarith

theorem row139 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L131 + (1 : ℝ) * (CF Γ p).H L158 + (-1 : ℝ) * (CF Γ p).H L527 + (-1 : ℝ) * (CF Γ p).H L164 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F18] L164 [F17]
  rw [show [F18] ++ L164 ++ [F17] = L528 from rfl, show [F18] ++ L164 = L523 from rfl,
    show L164 ++ [F17] = L526 from rfl] at hh
  rw [i264 h, i260 h, i263 h] at hh
  linarith

theorem row140 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L131 + (1 : ℝ) * (CF Γ p).H L113 + (-1 : ℝ) * (CF Γ p).H L530 + (-1 : ℝ) * (CF Γ p).H L164 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F18] L164 [F4]
  rw [show [F18] ++ L164 ++ [F4] = L531 from rfl, show [F18] ++ L164 = L523 from rfl,
    show L164 ++ [F4] = L529 from rfl] at hh
  rw [i266 h, i260 h, i265 h] at hh
  linarith

theorem row141 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L532 + (1 : ℝ) * (CF Γ p).H L96 + (-1 : ℝ) * (CF Γ p).H L443 + (-1 : ℝ) * (CF Γ p).H L65 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F18] L65 [F17]
  rw [show [F18] ++ L65 ++ [F17] = L534 from rfl, show [F18] ++ L65 = L533 from rfl,
    show L65 ++ [F17] = L336 from rfl] at hh
  rw [i268 h, i267 h, i147 h] at hh
  linarith

theorem row142 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L355 + (1 : ℝ) * (CF Γ p).H L141 + (-1 : ℝ) * (CF Γ p).H L537 + (-1 : ℝ) * (CF Γ p).H L194 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F18] L194 [F4]
  rw [show [F18] ++ L194 ++ [F4] = L538 from rfl, show [F18] ++ L194 = L535 from rfl,
    show L194 ++ [F4] = L536 from rfl] at hh
  rw [i271 h, i269 h, i270 h] at hh
  linarith

theorem row143 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L40 + (1 : ℝ) * (CF Γ p).H L540 + (-1 : ℝ) * (CF Γ p).H L230 + (-1 : ℝ) * (CF Γ p).H L54 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F22] L54 [F17]
  rw [show [F22] ++ L54 ++ [F17] = L542 from rfl, show [F22] ++ L54 = L539 from rfl,
    show L54 ++ [F17] = L541 from rfl] at hh
  rw [i274 h, i272 h, i273 h] at hh
  linarith

theorem row144 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L40 + (1 : ℝ) * (CF Γ p).H L544 + (-1 : ℝ) * (CF Γ p).H L546 + (-1 : ℝ) * (CF Γ p).H L115 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F22] L115 [F6]
  rw [show [F22] ++ L115 ++ [F6] = L547 from rfl, show [F22] ++ L115 = L543 from rfl,
    show L115 ++ [F6] = L545 from rfl] at hh
  rw [i277 h, i275 h, i276 h] at hh
  linarith

theorem row145 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L468 + (1 : ℝ) * (CF Γ p).H L549 + (-1 : ℝ) * (CF Γ p).H L332 + (-1 : ℝ) * (CF Γ p).H L26 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F22] L26 [F6]
  rw [show [F22] ++ L26 ++ [F6] = L551 from rfl, show [F22] ++ L26 = L548 from rfl,
    show L26 ++ [F6] = L550 from rfl] at hh
  rw [i280 h, i278 h, i279 h] at hh
  linarith

theorem row146 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L230 + (1 : ℝ) * (CF Γ p).H L220 + (-1 : ℝ) * (CF Γ p).H L556 + (-1 : ℝ) * (CF Γ p).H L559 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F22] L560 [F6]
  rw [show [F22] ++ L560 ++ [F6] = L557 from rfl, show [F22] ++ L560 = L552 from rfl,
    show L560 ++ [F6] = L554 from rfl] at hh
  rw [i283 h, i281 h, i282 h, i284 h] at hh
  linarith

theorem row147 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L230 + (1 : ℝ) * (CF Γ p).H L563 + (-1 : ℝ) * (CF Γ p).H L565 + (-1 : ℝ) * (CF Γ p).H L540 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F29] L567 [F4]
  rw [show [F29] ++ L567 ++ [F4] = L566 from rfl, show [F29] ++ L567 = L562 from rfl,
    show L567 ++ [F4] = L564 from rfl] at hh
  rw [i287 h, i285 h, i286 h, i288 h] at hh
  linarith

theorem row148 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L456 + (1 : ℝ) * (CF Γ p).H L569 + (-1 : ℝ) * (CF Γ p).H L302 + (-1 : ℝ) * (CF Γ p).H L100 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F22] L100 [F45]
  rw [show [F22] ++ L100 ++ [F45] = L571 from rfl, show [F22] ++ L100 = L568 from rfl,
    show L100 ++ [F45] = L570 from rfl] at hh
  rw [i291 h, i289 h, i290 h] at hh
  linarith

theorem row149 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L42 + (1 : ℝ) * (CF Γ p).H L172 + (-1 : ℝ) * (CF Γ p).H L575 + (-1 : ℝ) * (CF Γ p).H L62 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F22] L62 [F11]
  rw [show [F22] ++ L62 ++ [F11] = L576 from rfl, show [F22] ++ L62 = L573 from rfl,
    show L62 ++ [F11] = L574 from rfl] at hh
  rw [i294 h, i292 h, i293 h] at hh
  linarith

end EntropyBounds.GlueG.Certs.CL3B6SC
