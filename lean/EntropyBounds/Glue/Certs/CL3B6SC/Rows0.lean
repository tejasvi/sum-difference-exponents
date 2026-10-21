import EntropyBounds.Glue.Certs.CL3B6SC.Ids0
import EntropyBounds.Glue.Certs.CL3B6SC.Ids1
import EntropyBounds.Glue.Certs.CL3B6SC.Ids2
import EntropyBounds.Glue.Certs.CL3B6SC.Ids3
import EntropyBounds.Glue.Certs.CL3B6SC.Ids4
import EntropyBounds.Glue.Certs.CL3B6SC.Lemmas
import EntropyBounds.Glue.Lemma

set_option linter.unusedVariables false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open Finset

namespace EntropyBounds.Glue.Certs.CL3B6SC

open EntropyBounds.Iid EntropyBounds.Glue SumsDifferences SumsDifferences.NonShannon
open EntropyBounds.Lem

theorem row0 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L2 := by
  have hh := Conf.H_mono (hvF h).nonneg L3 [F10]
  rw [show L3 ++ [F10] = L1 from rfl] at hh
  rw [i0 h, i1 h] at hh
  linarith

theorem row1 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L5 := by
  have hh := Conf.H_mono (hvF h).nonneg L6 [F10]
  rw [show L6 ++ [F10] = L4 from rfl] at hh
  rw [i2 h, i3 h] at hh
  linarith

theorem row2 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L8 := by
  have hh := Conf.H_mono (hvF h).nonneg L9 [F10]
  rw [show L9 ++ [F10] = L7 from rfl] at hh
  rw [i4 h, i5 h] at hh
  linarith

theorem row3 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L10 + (1 : ℝ) * (CF Γ p).H L12 + (-1 : ℝ) * (CF Γ p).H L14 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F30] ([] : List (Form 6)) [F31]
  rw [show [F30] ++ ([] : List (Form 6)) ++ [F31] = L15 from rfl, show [F30] ++ ([] : List (Form 6)) = L11 from rfl,
    show ([] : List (Form 6)) ++ [F31] = L13 from rfl] at hh
  rw [i8 h, i6 h, i7 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row4 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L16 + (1 : ℝ) * (CF Γ p).H L18 + (-1 : ℝ) * (CF Γ p).H L20 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] ([] : List (Form 6)) [F5]
  rw [show [F10] ++ ([] : List (Form 6)) ++ [F5] = L21 from rfl, show [F10] ++ ([] : List (Form 6)) = L17 from rfl,
    show ([] : List (Form 6)) ++ [F5] = L19 from rfl] at hh
  rw [i11 h, i9 h, i10 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row5 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L22 + (1 : ℝ) * (CF Γ p).H L12 + (-1 : ℝ) * (CF Γ p).H L24 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F6] ([] : List (Form 6)) [F31]
  rw [show [F6] ++ ([] : List (Form 6)) ++ [F31] = L25 from rfl, show [F6] ++ ([] : List (Form 6)) = L23 from rfl,
    show ([] : List (Form 6)) ++ [F31] = L13 from rfl] at hh
  rw [i13 h, i12 h, i7 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row6 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L16 + (1 : ℝ) * (CF Γ p).H L26 + (-1 : ℝ) * (CF Γ p).H L28 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] ([] : List (Form 6)) [F34]
  rw [show [F10] ++ ([] : List (Form 6)) ++ [F34] = L29 from rfl, show [F10] ++ ([] : List (Form 6)) = L17 from rfl,
    show ([] : List (Form 6)) ++ [F34] = L27 from rfl] at hh
  rw [i15 h, i9 h, i14 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row7 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L16 + (1 : ℝ) * (CF Γ p).H L30 + (-1 : ℝ) * (CF Γ p).H L32 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] ([] : List (Form 6)) [F37]
  rw [show [F10] ++ ([] : List (Form 6)) ++ [F37] = L33 from rfl, show [F10] ++ ([] : List (Form 6)) = L17 from rfl,
    show ([] : List (Form 6)) ++ [F37] = L31 from rfl] at hh
  rw [i17 h, i9 h, i16 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row8 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L16 + (1 : ℝ) * (CF Γ p).H L34 + (-1 : ℝ) * (CF Γ p).H L36 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] ([] : List (Form 6)) [F38]
  rw [show [F10] ++ ([] : List (Form 6)) ++ [F38] = L37 from rfl, show [F10] ++ ([] : List (Form 6)) = L17 from rfl,
    show ([] : List (Form 6)) ++ [F38] = L35 from rfl] at hh
  rw [i19 h, i9 h, i18 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row9 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L38 + (1 : ℝ) * (CF Γ p).H L10 + (-1 : ℝ) * (CF Γ p).H L40 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F41] ([] : List (Form 6)) [F30]
  rw [show [F41] ++ ([] : List (Form 6)) ++ [F30] = L41 from rfl, show [F41] ++ ([] : List (Form 6)) = L39 from rfl,
    show ([] : List (Form 6)) ++ [F30] = L11 from rfl] at hh
  rw [i21 h, i20 h, i6 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row10 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L42 + (1 : ℝ) * (CF Γ p).H L10 + (-1 : ℝ) * (CF Γ p).H L44 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F43] ([] : List (Form 6)) [F30]
  rw [show [F43] ++ ([] : List (Form 6)) ++ [F30] = L45 from rfl, show [F43] ++ ([] : List (Form 6)) = L43 from rfl,
    show ([] : List (Form 6)) ++ [F30] = L11 from rfl] at hh
  rw [i23 h, i22 h, i6 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row11 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L42 + (1 : ℝ) * (CF Γ p).H L12 + (-1 : ℝ) * (CF Γ p).H L46 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F43] ([] : List (Form 6)) [F31]
  rw [show [F43] ++ ([] : List (Form 6)) ++ [F31] = L47 from rfl, show [F43] ++ ([] : List (Form 6)) = L43 from rfl,
    show ([] : List (Form 6)) ++ [F31] = L13 from rfl] at hh
  rw [i24 h, i22 h, i7 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row12 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L12 + (1 : ℝ) * (CF Γ p).H L48 + (-1 : ℝ) * (CF Γ p).H L50 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F31] ([] : List (Form 6)) [F46]
  rw [show [F31] ++ ([] : List (Form 6)) ++ [F46] = L51 from rfl, show [F31] ++ ([] : List (Form 6)) = L13 from rfl,
    show ([] : List (Form 6)) ++ [F46] = L49 from rfl] at hh
  rw [i26 h, i7 h, i25 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row13 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L10 + (1 : ℝ) * (CF Γ p).H L52 + (-1 : ℝ) * (CF Γ p).H L54 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F30] ([] : List (Form 6)) [F49]
  rw [show [F30] ++ ([] : List (Form 6)) ++ [F49] = L55 from rfl, show [F30] ++ ([] : List (Form 6)) = L11 from rfl,
    show ([] : List (Form 6)) ++ [F49] = L53 from rfl] at hh
  rw [i28 h, i6 h, i27 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row14 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L16 + (1 : ℝ) * (CF Γ p).H L57 + (-1 : ℝ) * (CF Γ p).H L54 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] ([] : List (Form 6)) [F51]
  rw [show [F10] ++ ([] : List (Form 6)) ++ [F51] = L59 from rfl, show [F10] ++ ([] : List (Form 6)) = L17 from rfl,
    show ([] : List (Form 6)) ++ [F51] = L58 from rfl] at hh
  rw [i30 h, i9 h, i29 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row15 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L16 + (1 : ℝ) * (CF Γ p).H L61 + (-1 : ℝ) * (CF Γ p).H L63 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] ([] : List (Form 6)) [F53]
  rw [show [F10] ++ ([] : List (Form 6)) ++ [F53] = L64 from rfl, show [F10] ++ ([] : List (Form 6)) = L17 from rfl,
    show ([] : List (Form 6)) ++ [F53] = L62 from rfl] at hh
  rw [i32 h, i9 h, i31 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row16 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L12 + (1 : ℝ) * (CF Γ p).H L66 + (-1 : ℝ) * (CF Γ p).H L68 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F31] ([] : List (Form 6)) [F55]
  rw [show [F31] ++ ([] : List (Form 6)) ++ [F55] = L69 from rfl, show [F31] ++ ([] : List (Form 6)) = L13 from rfl,
    show ([] : List (Form 6)) ++ [F55] = L67 from rfl] at hh
  rw [i34 h, i7 h, i33 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row17 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L16 + (1 : ℝ) * (CF Γ p).H L71 + (-1 : ℝ) * (CF Γ p).H L68 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] ([] : List (Form 6)) [F58]
  rw [show [F10] ++ ([] : List (Form 6)) ++ [F58] = L73 from rfl, show [F10] ++ ([] : List (Form 6)) = L17 from rfl,
    show ([] : List (Form 6)) ++ [F58] = L72 from rfl] at hh
  rw [i36 h, i9 h, i35 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row18 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L16 + (1 : ℝ) * (CF Γ p).H L75 + (-1 : ℝ) * (CF Γ p).H L77 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] ([] : List (Form 6)) [F17]
  rw [show [F10] ++ ([] : List (Form 6)) ++ [F17] = L78 from rfl, show [F10] ++ ([] : List (Form 6)) = L17 from rfl,
    show ([] : List (Form 6)) ++ [F17] = L76 from rfl] at hh
  rw [i38 h, i9 h, i37 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row19 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L10 + (1 : ℝ) * (CF Γ p).H L79 + (-1 : ℝ) * (CF Γ p).H L81 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F30] ([] : List (Form 6)) [F61]
  rw [show [F30] ++ ([] : List (Form 6)) ++ [F61] = L82 from rfl, show [F30] ++ ([] : List (Form 6)) = L11 from rfl,
    show ([] : List (Form 6)) ++ [F61] = L80 from rfl] at hh
  rw [i40 h, i6 h, i39 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row20 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L10 + (1 : ℝ) * (CF Γ p).H L83 + (-1 : ℝ) * (CF Γ p).H L85 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F30] ([] : List (Form 6)) [F63]
  rw [show [F30] ++ ([] : List (Form 6)) ++ [F63] = L86 from rfl, show [F30] ++ ([] : List (Form 6)) = L11 from rfl,
    show ([] : List (Form 6)) ++ [F63] = L84 from rfl] at hh
  rw [i42 h, i6 h, i41 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row21 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L12 + (1 : ℝ) * (CF Γ p).H L87 + (-1 : ℝ) * (CF Γ p).H L89 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F31] ([] : List (Form 6)) [F65]
  rw [show [F31] ++ ([] : List (Form 6)) ++ [F65] = L90 from rfl, show [F31] ++ ([] : List (Form 6)) = L13 from rfl,
    show ([] : List (Form 6)) ++ [F65] = L88 from rfl] at hh
  rw [i44 h, i7 h, i43 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row22 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L16 + (1 : ℝ) * (CF Γ p).H L91 + (-1 : ℝ) * (CF Γ p).H L93 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] ([] : List (Form 6)) [F67]
  rw [show [F10] ++ ([] : List (Form 6)) ++ [F67] = L94 from rfl, show [F10] ++ ([] : List (Form 6)) = L17 from rfl,
    show ([] : List (Form 6)) ++ [F67] = L92 from rfl] at hh
  rw [i46 h, i9 h, i45 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row23 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L10 + (1 : ℝ) * (CF Γ p).H L91 + (-1 : ℝ) * (CF Γ p).H L95 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F30] ([] : List (Form 6)) [F67]
  rw [show [F30] ++ ([] : List (Form 6)) ++ [F67] = L96 from rfl, show [F30] ++ ([] : List (Form 6)) = L11 from rfl,
    show ([] : List (Form 6)) ++ [F67] = L92 from rfl] at hh
  rw [i47 h, i6 h, i45 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row24 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L16 + (1 : ℝ) * (CF Γ p).H L97 + (-1 : ℝ) * (CF Γ p).H L99 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] ([] : List (Form 6)) [F69]
  rw [show [F10] ++ ([] : List (Form 6)) ++ [F69] = L100 from rfl, show [F10] ++ ([] : List (Form 6)) = L17 from rfl,
    show ([] : List (Form 6)) ++ [F69] = L98 from rfl] at hh
  rw [i49 h, i9 h, i48 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row25 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L10 + (1 : ℝ) * (CF Γ p).H L101 + (-1 : ℝ) * (CF Γ p).H L63 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F30] ([] : List (Form 6)) [F71]
  rw [show [F30] ++ ([] : List (Form 6)) ++ [F71] = L103 from rfl, show [F30] ++ ([] : List (Form 6)) = L11 from rfl,
    show ([] : List (Form 6)) ++ [F71] = L102 from rfl] at hh
  rw [i51 h, i6 h, i50 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row26 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L22 + (1 : ℝ) * (CF Γ p).H L105 + (-1 : ℝ) * (CF Γ p).H L107 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F6] ([] : List (Form 6)) [F7]
  rw [show [F6] ++ ([] : List (Form 6)) ++ [F7] = L108 from rfl, show [F6] ++ ([] : List (Form 6)) = L23 from rfl,
    show ([] : List (Form 6)) ++ [F7] = L106 from rfl] at hh
  rw [i53 h, i12 h, i52 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row27 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L22 + (1 : ℝ) * (CF Γ p).H L42 + (-1 : ℝ) * (CF Γ p).H L109 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F6] ([] : List (Form 6)) [F43]
  rw [show [F6] ++ ([] : List (Form 6)) ++ [F43] = L110 from rfl, show [F6] ++ ([] : List (Form 6)) = L23 from rfl,
    show ([] : List (Form 6)) ++ [F43] = L43 from rfl] at hh
  rw [i54 h, i12 h, i22 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row28 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L38 + (1 : ℝ) * (CF Γ p).H L105 + (-1 : ℝ) * (CF Γ p).H L111 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F41] ([] : List (Form 6)) [F7]
  rw [show [F41] ++ ([] : List (Form 6)) ++ [F7] = L112 from rfl, show [F41] ++ ([] : List (Form 6)) = L39 from rfl,
    show ([] : List (Form 6)) ++ [F7] = L106 from rfl] at hh
  rw [i55 h, i20 h, i52 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row29 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L26 + (1 : ℝ) * (CF Γ p).H L18 + (-1 : ℝ) * (CF Γ p).H L113 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F34] ([] : List (Form 6)) [F5]
  rw [show [F34] ++ ([] : List (Form 6)) ++ [F5] = L114 from rfl, show [F34] ++ ([] : List (Form 6)) = L27 from rfl,
    show ([] : List (Form 6)) ++ [F5] = L19 from rfl] at hh
  rw [i56 h, i14 h, i10 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row30 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L30 + (1 : ℝ) * (CF Γ p).H L18 + (-1 : ℝ) * (CF Γ p).H L115 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F37] ([] : List (Form 6)) [F5]
  rw [show [F37] ++ ([] : List (Form 6)) ++ [F5] = L116 from rfl, show [F37] ++ ([] : List (Form 6)) = L31 from rfl,
    show ([] : List (Form 6)) ++ [F5] = L19 from rfl] at hh
  rw [i57 h, i16 h, i10 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row31 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L22 + (1 : ℝ) * (CF Γ p).H L117 + (-1 : ℝ) * (CF Γ p).H L119 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F6] ([] : List (Form 6)) [F8]
  rw [show [F6] ++ ([] : List (Form 6)) ++ [F8] = L120 from rfl, show [F6] ++ ([] : List (Form 6)) = L23 from rfl,
    show ([] : List (Form 6)) ++ [F8] = L118 from rfl] at hh
  rw [i59 h, i12 h, i58 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row32 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L105 + (1 : ℝ) * (CF Γ p).H L121 + (-1 : ℝ) * (CF Γ p).H L123 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F7] ([] : List (Form 6)) [F73]
  rw [show [F7] ++ ([] : List (Form 6)) ++ [F73] = L124 from rfl, show [F7] ++ ([] : List (Form 6)) = L106 from rfl,
    show ([] : List (Form 6)) ++ [F73] = L122 from rfl] at hh
  rw [i61 h, i52 h, i60 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row33 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L18 + (1 : ℝ) * (CF Γ p).H L125 + (-1 : ℝ) * (CF Γ p).H L127 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F5] ([] : List (Form 6)) [F75]
  rw [show [F5] ++ ([] : List (Form 6)) ++ [F75] = L128 from rfl, show [F5] ++ ([] : List (Form 6)) = L19 from rfl,
    show ([] : List (Form 6)) ++ [F75] = L126 from rfl] at hh
  rw [i63 h, i10 h, i62 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row34 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L18 + (1 : ℝ) * (CF Γ p).H L129 + (-1 : ℝ) * (CF Γ p).H L131 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F5] ([] : List (Form 6)) [F77]
  rw [show [F5] ++ ([] : List (Form 6)) ++ [F77] = L132 from rfl, show [F5] ++ ([] : List (Form 6)) = L19 from rfl,
    show ([] : List (Form 6)) ++ [F77] = L130 from rfl] at hh
  rw [i65 h, i10 h, i64 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row35 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L18 + (1 : ℝ) * (CF Γ p).H L133 + (-1 : ℝ) * (CF Γ p).H L135 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F5] ([] : List (Form 6)) [F78]
  rw [show [F5] ++ ([] : List (Form 6)) ++ [F78] = L136 from rfl, show [F5] ++ ([] : List (Form 6)) = L19 from rfl,
    show ([] : List (Form 6)) ++ [F78] = L134 from rfl] at hh
  rw [i67 h, i10 h, i66 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row36 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L18 + (1 : ℝ) * (CF Γ p).H L137 + (-1 : ℝ) * (CF Γ p).H L139 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F5] ([] : List (Form 6)) [F80]
  rw [show [F5] ++ ([] : List (Form 6)) ++ [F80] = L140 from rfl, show [F5] ++ ([] : List (Form 6)) = L19 from rfl,
    show ([] : List (Form 6)) ++ [F80] = L138 from rfl] at hh
  rw [i69 h, i10 h, i68 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row37 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L18 + (1 : ℝ) * (CF Γ p).H L141 + (-1 : ℝ) * (CF Γ p).H L143 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F5] ([] : List (Form 6)) [F83]
  rw [show [F5] ++ ([] : List (Form 6)) ++ [F83] = L144 from rfl, show [F5] ++ ([] : List (Form 6)) = L19 from rfl,
    show ([] : List (Form 6)) ++ [F83] = L142 from rfl] at hh
  rw [i71 h, i10 h, i70 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row38 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L22 + (1 : ℝ) * (CF Γ p).H L75 + (-1 : ℝ) * (CF Γ p).H L145 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F6] ([] : List (Form 6)) [F17]
  rw [show [F6] ++ ([] : List (Form 6)) ++ [F17] = L146 from rfl, show [F6] ++ ([] : List (Form 6)) = L23 from rfl,
    show ([] : List (Form 6)) ++ [F17] = L76 from rfl] at hh
  rw [i72 h, i12 h, i37 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row39 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L18 + (1 : ℝ) * (CF Γ p).H L147 + (-1 : ℝ) * (CF Γ p).H L149 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F5] ([] : List (Form 6)) [F87]
  rw [show [F5] ++ ([] : List (Form 6)) ++ [F87] = L150 from rfl, show [F5] ++ ([] : List (Form 6)) = L19 from rfl,
    show ([] : List (Form 6)) ++ [F87] = L148 from rfl] at hh
  rw [i74 h, i10 h, i73 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row40 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L22 + (1 : ℝ) * (CF Γ p).H L152 + (-1 : ℝ) * (CF Γ p).H L154 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F6] ([] : List (Form 6)) [F89]
  rw [show [F6] ++ ([] : List (Form 6)) ++ [F89] = L155 from rfl, show [F6] ++ ([] : List (Form 6)) = L23 from rfl,
    show ([] : List (Form 6)) ++ [F89] = L153 from rfl] at hh
  rw [i76 h, i12 h, i75 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row41 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L105 + (1 : ℝ) * (CF Γ p).H L157 + (-1 : ℝ) * (CF Γ p).H L159 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F7] ([] : List (Form 6)) [F91]
  rw [show [F7] ++ ([] : List (Form 6)) ++ [F91] = L160 from rfl, show [F7] ++ ([] : List (Form 6)) = L106 from rfl,
    show ([] : List (Form 6)) ++ [F91] = L158 from rfl] at hh
  rw [i78 h, i52 h, i77 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row42 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L22 + (1 : ℝ) * (CF Γ p).H L161 + (-1 : ℝ) * (CF Γ p).H L163 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F6] ([] : List (Form 6)) [F93]
  rw [show [F6] ++ ([] : List (Form 6)) ++ [F93] = L164 from rfl, show [F6] ++ ([] : List (Form 6)) = L23 from rfl,
    show ([] : List (Form 6)) ++ [F93] = L162 from rfl] at hh
  rw [i80 h, i12 h, i79 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row43 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L22 + (1 : ℝ) * (CF Γ p).H L165 + (-1 : ℝ) * (CF Γ p).H L167 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F6] ([] : List (Form 6)) [F95]
  rw [show [F6] ++ ([] : List (Form 6)) ++ [F95] = L168 from rfl, show [F6] ++ ([] : List (Form 6)) = L23 from rfl,
    show ([] : List (Form 6)) ++ [F95] = L166 from rfl] at hh
  rw [i82 h, i12 h, i81 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row44 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L105 + (1 : ℝ) * (CF Γ p).H L97 + (-1 : ℝ) * (CF Γ p).H L169 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F7] ([] : List (Form 6)) [F69]
  rw [show [F7] ++ ([] : List (Form 6)) ++ [F69] = L170 from rfl, show [F7] ++ ([] : List (Form 6)) = L106 from rfl,
    show ([] : List (Form 6)) ++ [F69] = L98 from rfl] at hh
  rw [i83 h, i52 h, i48 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row45 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L18 + (1 : ℝ) * (CF Γ p).H L101 + (-1 : ℝ) * (CF Γ p).H L171 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F5] ([] : List (Form 6)) [F71]
  rw [show [F5] ++ ([] : List (Form 6)) ++ [F71] = L172 from rfl, show [F5] ++ ([] : List (Form 6)) = L19 from rfl,
    show ([] : List (Form 6)) ++ [F71] = L102 from rfl] at hh
  rw [i84 h, i10 h, i50 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row46 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L38 + (1 : ℝ) * (CF Γ p).H L42 + (-1 : ℝ) * (CF Γ p).H L173 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F41] ([] : List (Form 6)) [F43]
  rw [show [F41] ++ ([] : List (Form 6)) ++ [F43] = L174 from rfl, show [F41] ++ ([] : List (Form 6)) = L39 from rfl,
    show ([] : List (Form 6)) ++ [F43] = L43 from rfl] at hh
  rw [i85 h, i20 h, i22 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row47 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L26 + (1 : ℝ) * (CF Γ p).H L34 + (-1 : ℝ) * (CF Γ p).H L175 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F34] ([] : List (Form 6)) [F38]
  rw [show [F34] ++ ([] : List (Form 6)) ++ [F38] = L176 from rfl, show [F34] ++ ([] : List (Form 6)) = L27 from rfl,
    show ([] : List (Form 6)) ++ [F38] = L35 from rfl] at hh
  rw [i86 h, i14 h, i18 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row48 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L30 + (1 : ℝ) * (CF Γ p).H L34 + (-1 : ℝ) * (CF Γ p).H L177 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F37] ([] : List (Form 6)) [F38]
  rw [show [F37] ++ ([] : List (Form 6)) ++ [F38] = L178 from rfl, show [F37] ++ ([] : List (Form 6)) = L31 from rfl,
    show ([] : List (Form 6)) ++ [F38] = L35 from rfl] at hh
  rw [i87 h, i16 h, i18 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row49 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L34 + (1 : ℝ) * (CF Γ p).H L117 + (-1 : ℝ) * (CF Γ p).H L179 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F38] ([] : List (Form 6)) [F8]
  rw [show [F38] ++ ([] : List (Form 6)) ++ [F8] = L180 from rfl, show [F38] ++ ([] : List (Form 6)) = L35 from rfl,
    show ([] : List (Form 6)) ++ [F8] = L118 from rfl] at hh
  rw [i88 h, i18 h, i58 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row50 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L38 + (1 : ℝ) * (CF Γ p).H L181 + (-1 : ℝ) * (CF Γ p).H L183 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F41] ([] : List (Form 6)) [F15]
  rw [show [F41] ++ ([] : List (Form 6)) ++ [F15] = L184 from rfl, show [F41] ++ ([] : List (Form 6)) = L39 from rfl,
    show ([] : List (Form 6)) ++ [F15] = L182 from rfl] at hh
  rw [i90 h, i20 h, i89 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row51 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L42 + (1 : ℝ) * (CF Γ p).H L186 + (-1 : ℝ) * (CF Γ p).H L188 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F43] ([] : List (Form 6)) [F99]
  rw [show [F43] ++ ([] : List (Form 6)) ++ [F99] = L189 from rfl, show [F43] ++ ([] : List (Form 6)) = L43 from rfl,
    show ([] : List (Form 6)) ++ [F99] = L187 from rfl] at hh
  rw [i92 h, i22 h, i91 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row52 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L26 + (1 : ℝ) * (CF Γ p).H L186 + (-1 : ℝ) * (CF Γ p).H L190 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F34] ([] : List (Form 6)) [F99]
  rw [show [F34] ++ ([] : List (Form 6)) ++ [F99] = L191 from rfl, show [F34] ++ ([] : List (Form 6)) = L27 from rfl,
    show ([] : List (Form 6)) ++ [F99] = L187 from rfl] at hh
  rw [i93 h, i14 h, i91 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row53 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L30 + (1 : ℝ) * (CF Γ p).H L186 + (-1 : ℝ) * (CF Γ p).H L192 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F37] ([] : List (Form 6)) [F99]
  rw [show [F37] ++ ([] : List (Form 6)) ++ [F99] = L193 from rfl, show [F37] ++ ([] : List (Form 6)) = L31 from rfl,
    show ([] : List (Form 6)) ++ [F99] = L187 from rfl] at hh
  rw [i94 h, i16 h, i91 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row54 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L34 + (1 : ℝ) * (CF Γ p).H L186 + (-1 : ℝ) * (CF Γ p).H L194 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F38] ([] : List (Form 6)) [F99]
  rw [show [F38] ++ ([] : List (Form 6)) ++ [F99] = L195 from rfl, show [F38] ++ ([] : List (Form 6)) = L35 from rfl,
    show ([] : List (Form 6)) ++ [F99] = L187 from rfl] at hh
  rw [i95 h, i18 h, i91 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row55 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L30 + (1 : ℝ) * (CF Γ p).H L196 + (-1 : ℝ) * (CF Γ p).H L198 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F37] ([] : List (Form 6)) [F23]
  rw [show [F37] ++ ([] : List (Form 6)) ++ [F23] = L199 from rfl, show [F37] ++ ([] : List (Form 6)) = L31 from rfl,
    show ([] : List (Form 6)) ++ [F23] = L197 from rfl] at hh
  rw [i97 h, i16 h, i96 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row56 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L42 + (1 : ℝ) * (CF Γ p).H L133 + (-1 : ℝ) * (CF Γ p).H L201 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F43] ([] : List (Form 6)) [F78]
  rw [show [F43] ++ ([] : List (Form 6)) ++ [F78] = L202 from rfl, show [F43] ++ ([] : List (Form 6)) = L43 from rfl,
    show ([] : List (Form 6)) ++ [F78] = L134 from rfl] at hh
  rw [i98 h, i22 h, i66 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row57 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L34 + (1 : ℝ) * (CF Γ p).H L137 + (-1 : ℝ) * (CF Γ p).H L203 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F38] ([] : List (Form 6)) [F80]
  rw [show [F38] ++ ([] : List (Form 6)) ++ [F80] = L204 from rfl, show [F38] ++ ([] : List (Form 6)) = L35 from rfl,
    show ([] : List (Form 6)) ++ [F80] = L138 from rfl] at hh
  rw [i99 h, i18 h, i68 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row58 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L30 + (1 : ℝ) * (CF Γ p).H L75 + (-1 : ℝ) * (CF Γ p).H L205 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F37] ([] : List (Form 6)) [F17]
  rw [show [F37] ++ ([] : List (Form 6)) ++ [F17] = L206 from rfl, show [F37] ++ ([] : List (Form 6)) = L31 from rfl,
    show ([] : List (Form 6)) ++ [F17] = L76 from rfl] at hh
  rw [i100 h, i16 h, i37 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row59 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L38 + (1 : ℝ) * (CF Γ p).H L79 + (-1 : ℝ) * (CF Γ p).H L207 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F41] ([] : List (Form 6)) [F61]
  rw [show [F41] ++ ([] : List (Form 6)) ++ [F61] = L208 from rfl, show [F41] ++ ([] : List (Form 6)) = L39 from rfl,
    show ([] : List (Form 6)) ++ [F61] = L80 from rfl] at hh
  rw [i101 h, i20 h, i39 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row60 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L42 + (1 : ℝ) * (CF Γ p).H L209 + (-1 : ℝ) * (CF Γ p).H L211 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F43] ([] : List (Form 6)) [F25]
  rw [show [F43] ++ ([] : List (Form 6)) ++ [F25] = L212 from rfl, show [F43] ++ ([] : List (Form 6)) = L43 from rfl,
    show ([] : List (Form 6)) ++ [F25] = L210 from rfl] at hh
  rw [i103 h, i22 h, i102 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row61 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L38 + (1 : ℝ) * (CF Γ p).H L213 + (-1 : ℝ) * (CF Γ p).H L215 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F41] ([] : List (Form 6)) [F101]
  rw [show [F41] ++ ([] : List (Form 6)) ++ [F101] = L216 from rfl, show [F41] ++ ([] : List (Form 6)) = L39 from rfl,
    show ([] : List (Form 6)) ++ [F101] = L214 from rfl] at hh
  rw [i105 h, i20 h, i104 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row62 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L42 + (1 : ℝ) * (CF Γ p).H L218 + (-1 : ℝ) * (CF Γ p).H L220 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F43] ([] : List (Form 6)) [F102]
  rw [show [F43] ++ ([] : List (Form 6)) ++ [F102] = L221 from rfl, show [F43] ++ ([] : List (Form 6)) = L43 from rfl,
    show ([] : List (Form 6)) ++ [F102] = L219 from rfl] at hh
  rw [i107 h, i22 h, i106 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row63 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L34 + (1 : ℝ) * (CF Γ p).H L222 + (-1 : ℝ) * (CF Γ p).H L224 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F38] ([] : List (Form 6)) [F103]
  rw [show [F38] ++ ([] : List (Form 6)) ++ [F103] = L225 from rfl, show [F38] ++ ([] : List (Form 6)) = L35 from rfl,
    show ([] : List (Form 6)) ++ [F103] = L223 from rfl] at hh
  rw [i109 h, i18 h, i108 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row64 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L26 + (1 : ℝ) * (CF Γ p).H L91 + (-1 : ℝ) * (CF Γ p).H L227 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F34] ([] : List (Form 6)) [F67]
  rw [show [F34] ++ ([] : List (Form 6)) ++ [F67] = L228 from rfl, show [F34] ++ ([] : List (Form 6)) = L27 from rfl,
    show ([] : List (Form 6)) ++ [F67] = L92 from rfl] at hh
  rw [i110 h, i14 h, i45 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row65 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L34 + (1 : ℝ) * (CF Γ p).H L91 + (-1 : ℝ) * (CF Γ p).H L229 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F38] ([] : List (Form 6)) [F67]
  rw [show [F38] ++ ([] : List (Form 6)) ++ [F67] = L230 from rfl, show [F38] ++ ([] : List (Form 6)) = L35 from rfl,
    show ([] : List (Form 6)) ++ [F67] = L92 from rfl] at hh
  rw [i111 h, i18 h, i45 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row66 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L26 + (1 : ℝ) * (CF Γ p).H L97 + (-1 : ℝ) * (CF Γ p).H L231 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F34] ([] : List (Form 6)) [F69]
  rw [show [F34] ++ ([] : List (Form 6)) ++ [F69] = L232 from rfl, show [F34] ++ ([] : List (Form 6)) = L27 from rfl,
    show ([] : List (Form 6)) ++ [F69] = L98 from rfl] at hh
  rw [i112 h, i14 h, i48 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row67 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L26 + (1 : ℝ) * (CF Γ p).H L233 + (-1 : ℝ) * (CF Γ p).H L235 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F34] ([] : List (Form 6)) [F105]
  rw [show [F34] ++ ([] : List (Form 6)) ++ [F105] = L236 from rfl, show [F34] ++ ([] : List (Form 6)) = L27 from rfl,
    show ([] : List (Form 6)) ++ [F105] = L234 from rfl] at hh
  rw [i114 h, i14 h, i113 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row68 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L238 + (1 : ℝ) * (CF Γ p).H L240 + (-1 : ℝ) * (CF Γ p).H L242 + (-1 : ℝ) * (CF Γ p).H L10 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F7] L11 [F5]
  rw [show [F7] ++ L11 ++ [F5] = L243 from rfl, show [F7] ++ L11 = L239 from rfl,
    show L11 ++ [F5] = L241 from rfl] at hh
  rw [i117 h, i115 h, i116 h, i6 h] at hh
  linarith

theorem row69 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L238 + (1 : ℝ) * (CF Γ p).H L244 + (-1 : ℝ) * (CF Γ p).H L246 + (-1 : ℝ) * (CF Γ p).H L10 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F7] L11 [F73]
  rw [show [F7] ++ L11 ++ [F73] = L247 from rfl, show [F7] ++ L11 = L239 from rfl,
    show L11 ++ [F73] = L245 from rfl] at hh
  rw [i119 h, i115 h, i118 h, i6 h] at hh
  linarith

theorem row70 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L248 + (1 : ℝ) * (CF Γ p).H L250 + (-1 : ℝ) * (CF Γ p).H L252 + (-1 : ℝ) * (CF Γ p).H L12 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F7] L13 [F8]
  rw [show [F7] ++ L13 ++ [F8] = L253 from rfl, show [F7] ++ L13 = L249 from rfl,
    show L13 ++ [F8] = L251 from rfl] at hh
  rw [i122 h, i120 h, i121 h, i7 h] at hh
  linarith

theorem row71 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L121 + (1 : ℝ) * (CF Γ p).H L186 + (-1 : ℝ) * (CF Γ p).H L254 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F73] ([] : List (Form 6)) [F99]
  rw [show [F73] ++ ([] : List (Form 6)) ++ [F99] = L255 from rfl, show [F73] ++ ([] : List (Form 6)) = L122 from rfl,
    show ([] : List (Form 6)) ++ [F99] = L187 from rfl] at hh
  rw [i123 h, i60 h, i91 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row72 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L125 + (1 : ℝ) * (CF Γ p).H L186 + (-1 : ℝ) * (CF Γ p).H L257 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F75] ([] : List (Form 6)) [F99]
  rw [show [F75] ++ ([] : List (Form 6)) ++ [F99] = L258 from rfl, show [F75] ++ ([] : List (Form 6)) = L126 from rfl,
    show ([] : List (Form 6)) ++ [F99] = L187 from rfl] at hh
  rw [i124 h, i62 h, i91 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row73 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L186 + (1 : ℝ) * (CF Γ p).H L129 + (-1 : ℝ) * (CF Γ p).H L260 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F99] ([] : List (Form 6)) [F77]
  rw [show [F99] ++ ([] : List (Form 6)) ++ [F77] = L261 from rfl, show [F99] ++ ([] : List (Form 6)) = L187 from rfl,
    show ([] : List (Form 6)) ++ [F77] = L130 from rfl] at hh
  rw [i125 h, i91 h, i64 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row74 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L186 + (1 : ℝ) * (CF Γ p).H L263 + (-1 : ℝ) * (CF Γ p).H L265 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F99] ([] : List (Form 6)) [F106]
  rw [show [F99] ++ ([] : List (Form 6)) ++ [F106] = L266 from rfl, show [F99] ++ ([] : List (Form 6)) = L187 from rfl,
    show ([] : List (Form 6)) ++ [F106] = L264 from rfl] at hh
  rw [i127 h, i91 h, i126 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row75 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L48 + (1 : ℝ) * (CF Γ p).H L133 + (-1 : ℝ) * (CF Γ p).H L268 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F46] ([] : List (Form 6)) [F78]
  rw [show [F46] ++ ([] : List (Form 6)) ++ [F78] = L269 from rfl, show [F46] ++ ([] : List (Form 6)) = L49 from rfl,
    show ([] : List (Form 6)) ++ [F78] = L134 from rfl] at hh
  rw [i128 h, i25 h, i66 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row76 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L48 + (1 : ℝ) * (CF Γ p).H L137 + (-1 : ℝ) * (CF Γ p).H L271 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F46] ([] : List (Form 6)) [F80]
  rw [show [F46] ++ ([] : List (Form 6)) ++ [F80] = L272 from rfl, show [F46] ++ ([] : List (Form 6)) = L49 from rfl,
    show ([] : List (Form 6)) ++ [F80] = L138 from rfl] at hh
  rw [i129 h, i25 h, i68 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row77 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L133 + (1 : ℝ) * (CF Γ p).H L91 + (-1 : ℝ) * (CF Γ p).H L274 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F78] ([] : List (Form 6)) [F67]
  rw [show [F78] ++ ([] : List (Form 6)) ++ [F67] = L275 from rfl, show [F78] ++ ([] : List (Form 6)) = L134 from rfl,
    show ([] : List (Form 6)) ++ [F67] = L92 from rfl] at hh
  rw [i130 h, i66 h, i45 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row78 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L75 + (1 : ℝ) * (CF Γ p).H L209 + (-1 : ℝ) * (CF Γ p).H L277 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F17] ([] : List (Form 6)) [F25]
  rw [show [F17] ++ ([] : List (Form 6)) ++ [F25] = L278 from rfl, show [F17] ++ ([] : List (Form 6)) = L76 from rfl,
    show ([] : List (Form 6)) ++ [F25] = L210 from rfl] at hh
  rw [i131 h, i37 h, i102 h, Conf.H_nil (hvF h).nonneg (hvF h).sum_one] at hh
  linarith

theorem row79 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L280 + (1 : ℝ) * (CF Γ p).H L282 + (-1 : ℝ) * (CF Γ p).H L284 + (-1 : ℝ) * (CF Γ p).H L10 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L11 [F38]
  rw [show [F10] ++ L11 ++ [F38] = L285 from rfl, show [F10] ++ L11 = L281 from rfl,
    show L11 ++ [F38] = L283 from rfl] at hh
  rw [i134 h, i132 h, i133 h, i6 h] at hh
  linarith

theorem row80 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L280 + (1 : ℝ) * (CF Γ p).H L287 + (-1 : ℝ) * (CF Γ p).H L289 + (-1 : ℝ) * (CF Γ p).H L117 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L118 [F5]
  rw [show [F10] ++ L118 ++ [F5] = L290 from rfl, show [F10] ++ L118 = L286 from rfl,
    show L118 ++ [F5] = L288 from rfl] at hh
  rw [i137 h, i135 h, i136 h, i58 h] at hh
  linarith

theorem row81 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L28 + (1 : ℝ) * (CF Γ p).H L40 + (-1 : ℝ) * (CF Γ p).H L54 + (-1 : ℝ) * (CF Γ p).H L133 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L134 [F41]
  rw [show [F10] ++ L134 ++ [F41] = L293 from rfl, show [F10] ++ L134 = L291 from rfl,
    show L134 ++ [F41] = L292 from rfl] at hh
  rw [i140 h, i138 h, i139 h, i66 h] at hh
  linarith

theorem row82 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L28 + (1 : ℝ) * (CF Γ p).H L295 + (-1 : ℝ) * (CF Γ p).H L297 + (-1 : ℝ) * (CF Γ p).H L52 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L53 [F43]
  rw [show [F10] ++ L53 ++ [F43] = L298 from rfl, show [F10] ++ L53 = L294 from rfl,
    show L53 ++ [F43] = L296 from rfl] at hh
  rw [i143 h, i141 h, i142 h, i27 h] at hh
  linarith

theorem row83 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L28 + (1 : ℝ) * (CF Γ p).H L299 + (-1 : ℝ) * (CF Γ p).H L301 + (-1 : ℝ) * (CF Γ p).H L133 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L134 [F91]
  rw [show [F10] ++ L134 ++ [F91] = L302 from rfl, show [F10] ++ L134 = L291 from rfl,
    show L134 ++ [F91] = L300 from rfl] at hh
  rw [i145 h, i138 h, i144 h, i66 h] at hh
  linarith

theorem row84 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L54 + (1 : ℝ) * (CF Γ p).H L63 + (-1 : ℝ) * (CF Γ p).H L305 + (-1 : ℝ) * (CF Γ p).H L280 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F6] L281 [F7]
  rw [show [F6] ++ L281 ++ [F7] = L306 from rfl, show [F6] ++ L281 = L303 from rfl,
    show L281 ++ [F7] = L304 from rfl] at hh
  rw [i148 h, i146 h, i147 h, i132 h] at hh
  linarith

theorem row85 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L54 + (1 : ℝ) * (CF Γ p).H L254 + (-1 : ℝ) * (CF Γ p).H L311 + (-1 : ℝ) * (CF Γ p).H L314 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F30] L315 [F31]
  rw [show [F30] ++ L315 ++ [F31] = L312 from rfl, show [F30] ++ L315 = L307 from rfl,
    show L315 ++ [F31] = L309 from rfl] at hh
  rw [i151 h, i149 h, i150 h, i152 h] at hh
  linarith

theorem row86 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L32 + (1 : ℝ) * (CF Γ p).H L207 + (-1 : ℝ) * (CF Γ p).H L319 + (-1 : ℝ) * (CF Γ p).H L101 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L102 [F41]
  rw [show [F10] ++ L102 ++ [F41] = L320 from rfl, show [F10] ++ L102 = L317 from rfl,
    show L102 ++ [F41] = L318 from rfl] at hh
  rw [i155 h, i153 h, i154 h, i50 h] at hh
  linarith

theorem row87 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L32 + (1 : ℝ) * (CF Γ p).H L44 + (-1 : ℝ) * (CF Γ p).H L63 + (-1 : ℝ) * (CF Γ p).H L137 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L138 [F43]
  rw [show [F10] ++ L138 ++ [F43] = L323 from rfl, show [F10] ++ L138 = L321 from rfl,
    show L138 ++ [F43] = L322 from rfl] at hh
  rw [i158 h, i156 h, i157 h, i68 h] at hh
  linarith

theorem row88 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L32 + (1 : ℝ) * (CF Γ p).H L171 + (-1 : ℝ) * (CF Γ p).H L325 + (-1 : ℝ) * (CF Γ p).H L101 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L102 [F5]
  rw [show [F10] ++ L102 ++ [F5] = L326 from rfl, show [F10] ++ L102 = L317 from rfl,
    show L102 ++ [F5] = L324 from rfl] at hh
  rw [i160 h, i153 h, i159 h, i50 h] at hh
  linarith

theorem row89 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L32 + (1 : ℝ) * (CF Γ p).H L327 + (-1 : ℝ) * (CF Γ p).H L329 + (-1 : ℝ) * (CF Γ p).H L137 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L138 [F63]
  rw [show [F10] ++ L138 ++ [F63] = L330 from rfl, show [F10] ++ L138 = L321 from rfl,
    show L138 ++ [F63] = L328 from rfl] at hh
  rw [i162 h, i156 h, i161 h, i68 h] at hh
  linarith

theorem row90 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L331 + (1 : ℝ) * (CF Γ p).H L333 + (-1 : ℝ) * (CF Γ p).H L335 + (-1 : ℝ) * (CF Γ p).H L121 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L122 [F34]
  rw [show [F10] ++ L122 ++ [F34] = L336 from rfl, show [F10] ++ L122 = L332 from rfl,
    show L122 ++ [F34] = L334 from rfl] at hh
  rw [i165 h, i163 h, i164 h, i60 h] at hh
  linarith

theorem row91 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L331 + (1 : ℝ) * (CF Γ p).H L338 + (-1 : ℝ) * (CF Γ p).H L340 + (-1 : ℝ) * (CF Γ p).H L12 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L13 [F37]
  rw [show [F10] ++ L13 ++ [F37] = L341 from rfl, show [F10] ++ L13 = L337 from rfl,
    show L13 ++ [F37] = L339 from rfl] at hh
  rw [i168 h, i166 h, i167 h, i7 h] at hh
  linarith

theorem row92 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L331 + (1 : ℝ) * (CF Γ p).H L342 + (-1 : ℝ) * (CF Γ p).H L344 + (-1 : ℝ) * (CF Γ p).H L121 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L122 [F53]
  rw [show [F10] ++ L122 ++ [F53] = L345 from rfl, show [F10] ++ L122 = L332 from rfl,
    show L122 ++ [F53] = L343 from rfl] at hh
  rw [i170 h, i163 h, i169 h, i60 h] at hh
  linarith

theorem row93 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L20 + (1 : ℝ) * (CF Γ p).H L24 + (-1 : ℝ) * (CF Γ p).H L254 + (-1 : ℝ) * (CF Γ p).H L186 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L187 [F6]
  rw [show [F10] ++ L187 ++ [F6] = L349 from rfl, show [F10] ++ L187 = L347 from rfl,
    show L187 ++ [F6] = L348 from rfl] at hh
  rw [i173 h, i171 h, i172 h, i91 h] at hh
  linarith

theorem row94 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L254 + (1 : ℝ) * (CF Γ p).H L68 + (-1 : ℝ) * (CF Γ p).H L352 + (-1 : ℝ) * (CF Γ p).H L331 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F6] L337 [F7]
  rw [show [F6] ++ L337 ++ [F7] = L353 from rfl, show [F6] ++ L337 = L350 from rfl,
    show L337 ++ [F7] = L351 from rfl] at hh
  rw [i176 h, i174 h, i175 h, i166 h] at hh
  linarith

theorem row95 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L254 + (1 : ℝ) * (CF Γ p).H L356 + (-1 : ℝ) * (CF Γ p).H L359 + (-1 : ℝ) * (CF Γ p).H L362 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L363 [F37]
  rw [show [F10] ++ L363 ++ [F37] = L360 from rfl, show [F10] ++ L363 = L354 from rfl,
    show L363 ++ [F37] = L357 from rfl] at hh
  rw [i179 h, i177 h, i178 h, i180 h] at hh
  linarith

theorem row96 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L36 + (1 : ℝ) * (CF Γ p).H L163 + (-1 : ℝ) * (CF Γ p).H L367 + (-1 : ℝ) * (CF Γ p).H L66 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L67 [F6]
  rw [show [F10] ++ L67 ++ [F6] = L368 from rfl, show [F10] ++ L67 = L365 from rfl,
    show L67 ++ [F6] = L366 from rfl] at hh
  rw [i183 h, i181 h, i182 h, i33 h] at hh
  linarith

theorem row97 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L36 + (1 : ℝ) * (CF Γ p).H L143 + (-1 : ℝ) * (CF Γ p).H L371 + (-1 : ℝ) * (CF Γ p).H L141 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L142 [F5]
  rw [show [F10] ++ L142 ++ [F5] = L372 from rfl, show [F10] ++ L142 = L369 from rfl,
    show L142 ++ [F5] = L370 from rfl] at hh
  rw [i186 h, i184 h, i185 h, i70 h] at hh
  linarith

theorem row98 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L68 + (1 : ℝ) * (CF Γ p).H L374 + (-1 : ℝ) * (CF Γ p).H L376 + (-1 : ℝ) * (CF Γ p).H L46 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L47 [F34]
  rw [show [F10] ++ L47 ++ [F34] = L377 from rfl, show [F10] ++ L47 = L373 from rfl,
    show L47 ++ [F34] = L375 from rfl] at hh
  rw [i189 h, i187 h, i188 h, i24 h] at hh
  linarith

theorem row99 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L77 + (1 : ℝ) * (CF Γ p).H L113 + (-1 : ℝ) * (CF Γ p).H L379 + (-1 : ℝ) * (CF Γ p).H L75 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L76 [F34]
  rw [show [F10] ++ L76 ++ [F34] = L380 from rfl, show [F10] ++ L76 = L78 from rfl,
    show L76 ++ [F34] = L378 from rfl] at hh
  rw [i191 h, i38 h, i190 h, i37 h] at hh
  linarith

theorem row100 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L381 + (1 : ℝ) * (CF Γ p).H L383 + (-1 : ℝ) * (CF Γ p).H L301 + (-1 : ℝ) * (CF Γ p).H L83 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L84 [F34]
  rw [show [F10] ++ L84 ++ [F34] = L385 from rfl, show [F10] ++ L84 = L382 from rfl,
    show L84 ++ [F34] = L384 from rfl] at hh
  rw [i194 h, i192 h, i193 h, i41 h] at hh
  linarith

theorem row101 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L386 + (1 : ℝ) * (CF Γ p).H L388 + (-1 : ℝ) * (CF Γ p).H L390 + (-1 : ℝ) * (CF Γ p).H L165 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L166 [F38]
  rw [show [F10] ++ L166 ++ [F38] = L391 from rfl, show [F10] ++ L166 = L387 from rfl,
    show L166 ++ [F38] = L389 from rfl] at hh
  rw [i197 h, i195 h, i196 h, i81 h] at hh
  linarith

theorem row102 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L99 + (1 : ℝ) * (CF Γ p).H L85 + (-1 : ℝ) * (CF Γ p).H L394 + (-1 : ℝ) * (CF Γ p).H L222 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L223 [F30]
  rw [show [F10] ++ L223 ++ [F30] = L395 from rfl, show [F10] ++ L223 = L392 from rfl,
    show L223 ++ [F30] = L393 from rfl] at hh
  rw [i200 h, i198 h, i199 h, i108 h] at hh
  linarith

theorem row103 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L93 + (1 : ℝ) * (CF Γ p).H L397 + (-1 : ℝ) * (CF Γ p).H L399 + (-1 : ℝ) * (CF Γ p).H L233 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L234 [F7]
  rw [show [F10] ++ L234 ++ [F7] = L400 from rfl, show [F10] ++ L234 = L396 from rfl,
    show L234 ++ [F7] = L398 from rfl] at hh
  rw [i203 h, i201 h, i202 h, i113 h] at hh
  linarith

theorem row104 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L401 + (1 : ℝ) * (CF Γ p).H L403 + (-1 : ℝ) * (CF Γ p).H L215 + (-1 : ℝ) * (CF Γ p).H L161 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F41] L162 [F7]
  rw [show [F41] ++ L162 ++ [F7] = L405 from rfl, show [F41] ++ L162 = L402 from rfl,
    show L162 ++ [F7] = L404 from rfl] at hh
  rw [i206 h, i204 h, i205 h, i79 h] at hh
  linarith

theorem row105 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L403 + (1 : ℝ) * (CF Γ p).H L188 + (-1 : ℝ) * (CF Γ p).H L408 + (-1 : ℝ) * (CF Γ p).H L213 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F7] L214 [F43]
  rw [show [F7] ++ L214 ++ [F43] = L409 from rfl, show [F7] ++ L214 = L406 from rfl,
    show L214 ++ [F43] = L407 from rfl] at hh
  rw [i209 h, i207 h, i208 h, i104 h] at hh
  linarith

theorem row106 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L109 + (1 : ℝ) * (CF Γ p).H L411 + (-1 : ℝ) * (CF Γ p).H L413 + (-1 : ℝ) * (CF Γ p).H L48 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F6] L49 [F5]
  rw [show [F6] ++ L49 ++ [F5] = L414 from rfl, show [F6] ++ L49 = L410 from rfl,
    show L49 ++ [F5] = L412 from rfl] at hh
  rw [i212 h, i210 h, i211 h, i25 h] at hh
  linarith

theorem row107 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L415 + (1 : ℝ) * (CF Γ p).H L417 + (-1 : ℝ) * (CF Γ p).H L154 + (-1 : ℝ) * (CF Γ p).H L79 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F6] L80 [F7]
  rw [show [F6] ++ L80 ++ [F7] = L419 from rfl, show [F6] ++ L80 = L416 from rfl,
    show L80 ++ [F7] = L418 from rfl] at hh
  rw [i215 h, i213 h, i214 h, i39 h] at hh
  linarith

theorem row108 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L154 + (1 : ℝ) * (CF Γ p).H L352 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L107 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F30] L108 [F110]
  rw [show [F30] ++ L108 ++ [F110] = L423 from rfl, show [F30] ++ L108 = L420 from rfl,
    show L108 ++ [F110] = L421 from rfl] at hh
  rw [i218 h, i216 h, i217 h, i53 h] at hh
  linarith

theorem row109 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L425 + (1 : ℝ) * (CF Γ p).H L427 + (-1 : ℝ) * (CF Γ p).H L413 + (-1 : ℝ) * (CF Γ p).H L121 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F6] L122 [F43]
  rw [show [F6] ++ L122 ++ [F43] = L429 from rfl, show [F6] ++ L122 = L426 from rfl,
    show L122 ++ [F43] = L428 from rfl] at hh
  rw [i221 h, i219 h, i220 h, i60 h] at hh
  linarith

theorem row110 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L425 + (1 : ℝ) * (CF Γ p).H L430 + (-1 : ℝ) * (CF Γ p).H L432 + (-1 : ℝ) * (CF Γ p).H L121 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F6] L122 [F37]
  rw [show [F6] ++ L122 ++ [F37] = L433 from rfl, show [F6] ++ L122 = L426 from rfl,
    show L122 ++ [F37] = L431 from rfl] at hh
  rw [i223 h, i219 h, i222 h, i60 h] at hh
  linarith

theorem row111 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L434 + (1 : ℝ) * (CF Γ p).H L436 + (-1 : ℝ) * (CF Γ p).H L413 + (-1 : ℝ) * (CF Γ p).H L83 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F6] L84 [F43]
  rw [show [F6] ++ L84 ++ [F43] = L438 from rfl, show [F6] ++ L84 = L435 from rfl,
    show L84 ++ [F43] = L437 from rfl] at hh
  rw [i226 h, i224 h, i225 h, i41 h] at hh
  linarith

theorem row112 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L434 + (1 : ℝ) * (CF Γ p).H L439 + (-1 : ℝ) * (CF Γ p).H L441 + (-1 : ℝ) * (CF Γ p).H L83 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F6] L84 [F8]
  rw [show [F6] ++ L84 ++ [F8] = L442 from rfl, show [F6] ++ L84 = L435 from rfl,
    show L84 ++ [F8] = L440 from rfl] at hh
  rw [i228 h, i224 h, i227 h, i41 h] at hh
  linarith

theorem row113 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L119 + (1 : ℝ) * (CF Γ p).H L131 + (-1 : ℝ) * (CF Γ p).H L445 + (-1 : ℝ) * (CF Γ p).H L57 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F6] L58 [F5]
  rw [show [F6] ++ L58 ++ [F5] = L446 from rfl, show [F6] ++ L58 = L443 from rfl,
    show L58 ++ [F5] = L444 from rfl] at hh
  rw [i231 h, i229 h, i230 h, i29 h] at hh
  linarith

theorem row114 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L145 + (1 : ℝ) * (CF Γ p).H L169 + (-1 : ℝ) * (CF Γ p).H L449 + (-1 : ℝ) * (CF Γ p).H L218 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F6] L219 [F7]
  rw [show [F6] ++ L219 ++ [F7] = L450 from rfl, show [F6] ++ L219 = L447 from rfl,
    show L219 ++ [F7] = L448 from rfl] at hh
  rw [i234 h, i232 h, i233 h, i106 h] at hh
  linarith

theorem row115 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L145 + (1 : ℝ) * (CF Γ p).H L451 + (-1 : ℝ) * (CF Γ p).H L453 + (-1 : ℝ) * (CF Γ p).H L218 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F6] L219 [F37]
  rw [show [F6] ++ L219 ++ [F37] = L454 from rfl, show [F6] ++ L219 = L447 from rfl,
    show L219 ++ [F37] = L452 from rfl] at hh
  rw [i236 h, i232 h, i235 h, i106 h] at hh
  linarith

theorem row116 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L145 + (1 : ℝ) * (CF Γ p).H L455 + (-1 : ℝ) * (CF Γ p).H L457 + (-1 : ℝ) * (CF Γ p).H L218 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F6] L219 [F67]
  rw [show [F6] ++ L219 ++ [F67] = L458 from rfl, show [F6] ++ L219 = L447 from rfl,
    show L219 ++ [F67] = L456 from rfl] at hh
  rw [i238 h, i232 h, i237 h, i106 h] at hh
  linarith

theorem row117 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L167 + (1 : ℝ) * (CF Γ p).H L203 + (-1 : ℝ) * (CF Γ p).H L461 + (-1 : ℝ) * (CF Γ p).H L147 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F6] L148 [F38]
  rw [show [F6] ++ L148 ++ [F38] = L462 from rfl, show [F6] ++ L148 = L459 from rfl,
    show L148 ++ [F38] = L460 from rfl] at hh
  rw [i241 h, i239 h, i240 h, i73 h] at hh
  linarith

theorem row118 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L463 + (1 : ℝ) * (CF Γ p).H L220 + (-1 : ℝ) * (CF Γ p).H L466 + (-1 : ℝ) * (CF Γ p).H L222 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F6] L223 [F43]
  rw [show [F6] ++ L223 ++ [F43] = L467 from rfl, show [F6] ++ L223 = L464 from rfl,
    show L223 ++ [F43] = L465 from rfl] at hh
  rw [i244 h, i242 h, i243 h, i108 h] at hh
  linarith

theorem row119 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L463 + (1 : ℝ) * (CF Γ p).H L139 + (-1 : ℝ) * (CF Γ p).H L469 + (-1 : ℝ) * (CF Γ p).H L222 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F6] L223 [F5]
  rw [show [F6] ++ L223 ++ [F5] = L470 from rfl, show [F6] ++ L223 = L464 from rfl,
    show L223 ++ [F5] = L468 from rfl] at hh
  rw [i246 h, i242 h, i245 h, i108 h] at hh
  linarith

theorem row120 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L463 + (1 : ℝ) * (CF Γ p).H L472 + (-1 : ℝ) * (CF Γ p).H L474 + (-1 : ℝ) * (CF Γ p).H L157 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F6] L158 [F8]
  rw [show [F6] ++ L158 ++ [F8] = L475 from rfl, show [F6] ++ L158 = L471 from rfl,
    show L158 ++ [F8] = L473 from rfl] at hh
  rw [i249 h, i247 h, i248 h, i77 h] at hh
  linarith

theorem row121 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L476 + (1 : ℝ) * (CF Γ p).H L115 + (-1 : ℝ) * (CF Γ p).H L432 + (-1 : ℝ) * (CF Γ p).H L97 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F6] L98 [F37]
  rw [show [F6] ++ L98 ++ [F37] = L479 from rfl, show [F6] ++ L98 = L477 from rfl,
    show L98 ++ [F37] = L478 from rfl] at hh
  rw [i252 h, i250 h, i251 h, i48 h] at hh
  linarith

theorem row122 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L417 + (1 : ℝ) * (CF Γ p).H L201 + (-1 : ℝ) * (CF Γ p).H L297 + (-1 : ℝ) * (CF Γ p).H L152 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F7] L153 [F43]
  rw [show [F7] ++ L153 ++ [F43] = L482 from rfl, show [F7] ++ L153 = L480 from rfl,
    show L153 ++ [F43] = L481 from rfl] at hh
  rw [i255 h, i253 h, i254 h, i75 h] at hh
  linarith

theorem row123 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L417 + (1 : ℝ) * (CF Γ p).H L484 + (-1 : ℝ) * (CF Γ p).H L486 + (-1 : ℝ) * (CF Γ p).H L79 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F7] L80 [F5]
  rw [show [F7] ++ L80 ++ [F5] = L487 from rfl, show [F7] ++ L80 = L483 from rfl,
    show L80 ++ [F5] = L485 from rfl] at hh
  rw [i258 h, i256 h, i257 h, i39 h] at hh
  linarith

theorem row124 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L173 + (1 : ℝ) * (CF Γ p).H L489 + (-1 : ℝ) * (CF Γ p).H L491 + (-1 : ℝ) * (CF Γ p).H L125 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F41] L126 [F34]
  rw [show [F41] ++ L126 ++ [F34] = L492 from rfl, show [F41] ++ L126 = L488 from rfl,
    show L126 ++ [F34] = L490 from rfl] at hh
  rw [i261 h, i259 h, i260 h, i62 h] at hh
  linarith

theorem row125 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L401 + (1 : ℝ) * (CF Γ p).H L493 + (-1 : ℝ) * (CF Γ p).H L495 + (-1 : ℝ) * (CF Γ p).H L161 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F41] L162 [F17]
  rw [show [F41] ++ L162 ++ [F17] = L496 from rfl, show [F41] ++ L162 = L402 from rfl,
    show L162 ++ [F17] = L494 from rfl] at hh
  rw [i263 h, i204 h, i262 h, i79 h] at hh
  linarith

theorem row126 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L497 + (1 : ℝ) * (CF Γ p).H L499 + (-1 : ℝ) * (CF Γ p).H L491 + (-1 : ℝ) * (CF Γ p).H L117 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F41] L118 [F43]
  rw [show [F41] ++ L118 ++ [F43] = L501 from rfl, show [F41] ++ L118 = L498 from rfl,
    show L118 ++ [F43] = L500 from rfl] at hh
  rw [i266 h, i264 h, i265 h, i58 h] at hh
  linarith

theorem row127 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L497 + (1 : ℝ) * (CF Γ p).H L179 + (-1 : ℝ) * (CF Γ p).H L503 + (-1 : ℝ) * (CF Γ p).H L117 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F41] L118 [F38]
  rw [show [F41] ++ L118 ++ [F38] = L504 from rfl, show [F41] ++ L118 = L498 from rfl,
    show L118 ++ [F38] = L502 from rfl] at hh
  rw [i268 h, i264 h, i267 h, i58 h] at hh
  linarith

theorem row128 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L497 + (1 : ℝ) * (CF Γ p).H L505 + (-1 : ℝ) * (CF Γ p).H L507 + (-1 : ℝ) * (CF Γ p).H L117 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F41] L118 [F73]
  rw [show [F41] ++ L118 ++ [F73] = L508 from rfl, show [F41] ++ L118 = L498 from rfl,
    show L118 ++ [F73] = L506 from rfl] at hh
  rw [i270 h, i264 h, i269 h, i58 h] at hh
  linarith

theorem row129 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L509 + (1 : ℝ) * (CF Γ p).H L511 + (-1 : ℝ) * (CF Γ p).H L491 + (-1 : ℝ) * (CF Γ p).H L87 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F41] L88 [F43]
  rw [show [F41] ++ L88 ++ [F43] = L513 from rfl, show [F41] ++ L88 = L510 from rfl,
    show L88 ++ [F43] = L512 from rfl] at hh
  rw [i273 h, i271 h, i272 h, i43 h] at hh
  linarith

theorem row130 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L305 + (1 : ℝ) * (CF Γ p).H L516 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L268 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L521 [F31]
  rw [show [F10] ++ L521 ++ [F31] = L519 from rfl, show [F10] ++ L521 = L514 from rfl,
    show L521 ++ [F31] = L517 from rfl] at hh
  rw [i276 h, i274 h, i275 h, i277 h] at hh
  linarith

theorem row131 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L305 + (1 : ℝ) * (CF Γ p).H L524 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L527 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L528 [F31]
  rw [show [F10] ++ L528 ++ [F31] = L526 from rfl, show [F10] ++ L528 = L523 from rfl,
    show L528 ++ [F31] = L525 from rfl] at hh
  rw [i280 h, i278 h, i279 h, i281 h] at hh
  linarith

theorem row132 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L305 + (1 : ℝ) * (CF Γ p).H L530 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L533 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L534 [F5]
  rw [show [F10] ++ L534 ++ [F5] = L532 from rfl, show [F10] ++ L534 = L529 from rfl,
    show L534 ++ [F5] = L531 from rfl] at hh
  rw [i284 h, i282 h, i283 h, i285 h] at hh
  linarith

theorem row133 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L352 + (1 : ℝ) * (CF Γ p).H L537 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L257 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L542 [F30]
  rw [show [F10] ++ L542 ++ [F30] = L540 from rfl, show [F10] ++ L542 = L535 from rfl,
    show L542 ++ [F30] = L538 from rfl] at hh
  rw [i288 h, i286 h, i287 h, i289 h] at hh
  linarith

theorem row134 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L352 + (1 : ℝ) * (CF Γ p).H L545 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L548 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F10] L549 [F30]
  rw [show [F10] ++ L549 ++ [F30] = L547 from rfl, show [F10] ++ L549 = L544 from rfl,
    show L549 ++ [F30] = L546 from rfl] at hh
  rw [i292 h, i290 h, i291 h, i293 h] at hh
  linarith

theorem row135 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L352 + (1 : ℝ) * (CF Γ p).H L551 + (-1 : ℝ) * (CF Γ p).H L0 + (-1 : ℝ) * (CF Γ p).H L554 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F6] L555 [F34]
  rw [show [F6] ++ L555 ++ [F34] = L553 from rfl, show [F6] ++ L555 = L550 from rfl,
    show L555 ++ [F34] = L552 from rfl] at hh
  rw [i296 h, i294 h, i295 h, i297 h] at hh
  linarith

theorem row136 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L123 + (1 : ℝ) * (CF Γ p).H L227 + (-1 : ℝ) * (CF Γ p).H L558 + (-1 : ℝ) * (CF Γ p).H L71 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F7] L72 [F34]
  rw [show [F7] ++ L72 ++ [F34] = L559 from rfl, show [F7] ++ L72 = L556 from rfl,
    show L72 ++ [F34] = L557 from rfl] at hh
  rw [i300 h, i298 h, i299 h, i35 h] at hh
  linarith

theorem row137 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L560 + (1 : ℝ) * (CF Γ p).H L562 + (-1 : ℝ) * (CF Γ p).H L352 + (-1 : ℝ) * (CF Γ p).H L83 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F7] L84 [F73]
  rw [show [F7] ++ L84 ++ [F73] = L564 from rfl, show [F7] ++ L84 = L561 from rfl,
    show L84 ++ [F73] = L563 from rfl] at hh
  rw [i303 h, i301 h, i302 h, i41 h] at hh
  linarith

theorem row138 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L159 + (1 : ℝ) * (CF Γ p).H L14 + (-1 : ℝ) * (CF Γ p).H L198 + (-1 : ℝ) * (CF Γ p).H L196 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F7] L197 [F30]
  rw [show [F7] ++ L197 ++ [F30] = L568 from rfl, show [F7] ++ L197 = L566 from rfl,
    show L197 ++ [F30] = L567 from rfl] at hh
  rw [i306 h, i304 h, i305 h, i96 h] at hh
  linarith

theorem row139 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L159 + (1 : ℝ) * (CF Γ p).H L190 + (-1 : ℝ) * (CF Γ p).H L570 + (-1 : ℝ) * (CF Γ p).H L196 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F7] L197 [F34]
  rw [show [F7] ++ L197 ++ [F34] = L571 from rfl, show [F7] ++ L197 = L566 from rfl,
    show L197 ++ [F34] = L569 from rfl] at hh
  rw [i308 h, i304 h, i307 h, i96 h] at hh
  linarith

theorem row140 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L159 + (1 : ℝ) * (CF Γ p).H L135 + (-1 : ℝ) * (CF Γ p).H L573 + (-1 : ℝ) * (CF Γ p).H L196 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F7] L197 [F5]
  rw [show [F7] ++ L197 ++ [F5] = L574 from rfl, show [F7] ++ L197 = L566 from rfl,
    show L197 ++ [F5] = L572 from rfl] at hh
  rw [i310 h, i304 h, i309 h, i96 h] at hh
  linarith

theorem row141 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L575 + (1 : ℝ) * (CF Γ p).H L113 + (-1 : ℝ) * (CF Γ p).H L486 + (-1 : ℝ) * (CF Γ p).H L75 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F7] L76 [F34]
  rw [show [F7] ++ L76 ++ [F34] = L577 from rfl, show [F7] ++ L76 = L576 from rfl,
    show L76 ++ [F34] = L378 from rfl] at hh
  rw [i312 h, i311 h, i190 h, i37 h] at hh
  linarith

theorem row142 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L397 + (1 : ℝ) * (CF Γ p).H L171 + (-1 : ℝ) * (CF Γ p).H L580 + (-1 : ℝ) * (CF Γ p).H L233 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F7] L234 [F5]
  rw [show [F7] ++ L234 ++ [F5] = L581 from rfl, show [F7] ++ L234 = L578 from rfl,
    show L234 ++ [F5] = L579 from rfl] at hh
  rw [i315 h, i313 h, i314 h, i113 h] at hh
  linarith

theorem row143 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L44 + (1 : ℝ) * (CF Γ p).H L583 + (-1 : ℝ) * (CF Γ p).H L271 + (-1 : ℝ) * (CF Γ p).H L61 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F43] L62 [F34]
  rw [show [F43] ++ L62 ++ [F34] = L585 from rfl, show [F43] ++ L62 = L582 from rfl,
    show L62 ++ [F34] = L584 from rfl] at hh
  rw [i318 h, i316 h, i317 h, i31 h] at hh
  linarith

theorem row144 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L44 + (1 : ℝ) * (CF Γ p).H L587 + (-1 : ℝ) * (CF Γ p).H L589 + (-1 : ℝ) * (CF Γ p).H L137 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F43] L138 [F31]
  rw [show [F43] ++ L138 ++ [F31] = L590 from rfl, show [F43] ++ L138 = L586 from rfl,
    show L138 ++ [F31] = L588 from rfl] at hh
  rw [i321 h, i319 h, i320 h, i68 h] at hh
  linarith

theorem row145 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L511 + (1 : ℝ) * (CF Γ p).H L592 + (-1 : ℝ) * (CF Γ p).H L374 + (-1 : ℝ) * (CF Γ p).H L26 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F43] L27 [F31]
  rw [show [F43] ++ L27 ++ [F31] = L594 from rfl, show [F43] ++ L27 = L591 from rfl,
    show L27 ++ [F31] = L593 from rfl] at hh
  rw [i324 h, i322 h, i323 h, i14 h] at hh
  linarith

theorem row146 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L271 + (1 : ℝ) * (CF Γ p).H L260 + (-1 : ℝ) * (CF Γ p).H L599 + (-1 : ℝ) * (CF Γ p).H L602 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F43] L603 [F31]
  rw [show [F43] ++ L603 ++ [F31] = L600 from rfl, show [F43] ++ L603 = L595 from rfl,
    show L603 ++ [F31] = L597 from rfl] at hh
  rw [i327 h, i325 h, i326 h, i328 h] at hh
  linarith

theorem row147 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L271 + (1 : ℝ) * (CF Γ p).H L606 + (-1 : ℝ) * (CF Γ p).H L608 + (-1 : ℝ) * (CF Γ p).H L583 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F6] L610 [F5]
  rw [show [F6] ++ L610 ++ [F5] = L609 from rfl, show [F6] ++ L610 = L605 from rfl,
    show L610 ++ [F5] = L607 from rfl] at hh
  rw [i331 h, i329 h, i330 h, i332 h] at hh
  linarith

theorem row148 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L499 + (1 : ℝ) * (CF Γ p).H L612 + (-1 : ℝ) * (CF Γ p).H L344 + (-1 : ℝ) * (CF Γ p).H L117 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F43] L118 [F9]
  rw [show [F43] ++ L118 ++ [F9] = L614 from rfl, show [F43] ++ L118 = L611 from rfl,
    show L118 ++ [F9] = L613 from rfl] at hh
  rw [i335 h, i333 h, i334 h, i58 h] at hh
  linarith

theorem row149 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    0 ≤ (1 : ℝ) * (CF Γ p).H L46 + (1 : ℝ) * (CF Γ p).H L205 + (-1 : ℝ) * (CF Γ p).H L618 + (-1 : ℝ) * (CF Γ p).H L71 := by
  have hh := Conf.H_submod (hvF h).nonneg (hvF h).sum_one [F43] L72 [F37]
  rw [show [F43] ++ L72 ++ [F37] = L619 from rfl, show [F43] ++ L72 = L616 from rfl,
    show L72 ++ [F37] = L617 from rfl] at hh
  rw [i338 h, i336 h, i337 h, i35 h] at hh
  linarith

end EntropyBounds.Glue.Certs.CL3B6SC
