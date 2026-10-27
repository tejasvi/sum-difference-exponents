import EntropyBounds.GlueZ.Certs.C3BALL.Ids0
import EntropyBounds.GlueZ.Certs.C3BALL.Ids1

set_option linter.unusedVariables false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open Finset

namespace EntropyBounds.GlueZ.Certs.C3BALL

variable {G : Type} [AddCommGroup G] [DecidableEq G]

open EntropyBounds.Iid EntropyBounds.GlueG EntropyBounds.GlueZ SumsDifferences SumsDifferences.NonShannon

theorem row150 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    (1 : ℝ) * (CF Γ p).H L79 + (-1 : ℝ) * (CF Γ p).H L69 = 0 := by
  have hh : (C2 Γ p).H (L587 ++ L6) = (C2 Γ p).H (L226 ++ L6) :=
    Conf.H_copy_eqlaw (src := src1) (V := V1) (hv1 h) (by decide) L587 L6 L226 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L587 ++ L6 = L589 from rfl, show L226 ++ L6 = L591 from rfl] at hh
  rw [← lift2 h L591 (by decide), ← lift2 h L589 (by decide)] at hh
  rw [i339 h, i338 h] at hh
  linarith

theorem row151 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    (1 : ℝ) * (CF Γ p).H L260 + (-1 : ℝ) * (CF Γ p).H L53 = 0 := by
  have hh : (C2 Γ p).H (L14 ++ L6) = (C2 Γ p).H (L23 ++ L6) :=
    Conf.H_copy_eqlaw (src := src1) (V := V1) (hv1 h) (by decide) L14 L6 L23 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L14 ++ L6 = L593 from rfl, show L23 ++ L6 = L594 from rfl] at hh
  rw [← lift2 h L594 (by decide), ← lift2 h L593 (by decide)] at hh
  rw [i341 h, i340 h] at hh
  linarith

theorem row152 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    (1 : ℝ) * (CF Γ p).H L309 + (-1 : ℝ) * (CF Γ p).H L88 = 0 := by
  have hh : (C2 Γ p).H (L595 ++ ([] : List (Form 6))) = (C2 Γ p).H (L596 ++ ([] : List (Form 6))) :=
    Conf.H_copy_eqlaw (src := src1) (V := V1) (hv1 h) (by decide) L595 ([] : List (Form 6)) L596 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L595 ++ ([] : List (Form 6)) = L595 from rfl, show L596 ++ ([] : List (Form 6)) = L596 from rfl] at hh
  rw [← lift2 h L596 (by decide), ← lift2 h L595 (by decide)] at hh
  rw [i343 h, i342 h] at hh
  linarith

theorem row153 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    (1 : ℝ) * (CF Γ p).H L262 + (-1 : ℝ) * (CF Γ p).H L55 = 0 := by
  have hh : (C2 Γ p).H (L11 ++ L50) = (C2 Γ p).H (L18 ++ L50) :=
    Conf.H_copy_eqlaw (src := src1) (V := V1) (hv1 h) (by decide) L11 L50 L18 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L11 ++ L50 = L597 from rfl, show L18 ++ L50 = L56 from rfl] at hh
  rw [← lift2 h L56 (by decide), ← lift2 h L597 (by decide)] at hh
  rw [i21 h, i344 h] at hh
  linarith

theorem row154 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    (1 : ℝ) * (CF Γ p).H L7 + (-1 : ℝ) * (CF Γ p).H L0 = 0 := by
  have hh : (CF Γ p).H (L8 ++ ([] : List (Form 6))) = (CF Γ p).H (L1 ++ ([] : List (Form 6))) :=
    Conf.H_copy_eqlaw (src := src2) (V := V2) (hv2 h) (by decide) L8 ([] : List (Form 6)) L1 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L8 ++ ([] : List (Form 6)) = L8 from rfl, show L1 ++ ([] : List (Form 6)) = L1 from rfl] at hh
  rw [i0 h, i3 h] at hh
  linarith

theorem row155 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    (1 : ℝ) * (CF Γ p).H L2 + (-1 : ℝ) * (CF Γ p).H L5 = 0 := by
  have hh : (CF Γ p).H (L2 ++ ([] : List (Form 6))) = (CF Γ p).H (L6 ++ ([] : List (Form 6))) :=
    Conf.H_copy_eqlaw (src := src2) (V := V2) (hv2 h) (by decide) L2 ([] : List (Form 6)) L6 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L2 ++ ([] : List (Form 6)) = L2 from rfl, show L6 ++ ([] : List (Form 6)) = L6 from rfl] at hh
  rw [i2 h] at hh
  linarith

theorem row156 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    (1 : ℝ) * (CF Γ p).H L383 + (-1 : ℝ) * (CF Γ p).H L170 = 0 := by
  have hh : (CF Γ p).H (L384 ++ ([] : List (Form 6))) = (CF Γ p).H (L171 ++ ([] : List (Form 6))) :=
    Conf.H_copy_eqlaw (src := src2) (V := V2) (hv2 h) (by decide) L384 ([] : List (Form 6)) L171 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L384 ++ ([] : List (Form 6)) = L384 from rfl, show L171 ++ ([] : List (Form 6)) = L171 from rfl] at hh
  rw [i71 h, i198 h] at hh
  linarith

theorem row157 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    (1 : ℝ) * (CF Γ p).H L90 + (-1 : ℝ) * (CF Γ p).H L23 = 0 := by
  have hh : (CF Γ p).H (L90 ++ ([] : List (Form 6))) = (CF Γ p).H (L23 ++ ([] : List (Form 6))) :=
    Conf.H_copy_eqlaw (src := src2) (V := V2) (hv2 h) (by decide) L90 ([] : List (Form 6)) L23 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L90 ++ ([] : List (Form 6)) = L90 from rfl, show L23 ++ ([] : List (Form 6)) = L23 from rfl] at hh
  linarith

theorem row158 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    (1 : ℝ) * (CF Γ p).H L235 + (-1 : ℝ) * (CF Γ p).H L225 = 0 := by
  have hh : (CF Γ p).H (L236 ++ ([] : List (Form 6))) = (CF Γ p).H (L226 ++ ([] : List (Form 6))) :=
    Conf.H_copy_eqlaw (src := src2) (V := V2) (hv2 h) (by decide) L236 ([] : List (Form 6)) L226 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L236 ++ ([] : List (Form 6)) = L236 from rfl, show L226 ++ ([] : List (Form 6)) = L226 from rfl] at hh
  rw [i104 h, i108 h] at hh
  linarith

theorem row159 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    (1 : ℝ) * (CF Γ p).H L255 + (-1 : ℝ) * (CF Γ p).H L69 = 0 := by
  have hh : (CF Γ p).H (L598 ++ ([] : List (Form 6))) = (CF Γ p).H (L591 ++ ([] : List (Form 6))) :=
    Conf.H_copy_eqlaw (src := src2) (V := V2) (hv2 h) (by decide) L598 ([] : List (Form 6)) L591 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L598 ++ ([] : List (Form 6)) = L598 from rfl, show L591 ++ ([] : List (Form 6)) = L591 from rfl] at hh
  rw [i339 h, i345 h] at hh
  linarith

theorem row160 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    (1 : ℝ) * (CF Γ p).H L240 + (-1 : ℝ) * (CF Γ p).H L53 = 0 := by
  have hh : (CF Γ p).H (L600 ++ ([] : List (Form 6))) = (CF Γ p).H (L594 ++ ([] : List (Form 6))) :=
    Conf.H_copy_eqlaw (src := src2) (V := V2) (hv2 h) (by decide) L600 ([] : List (Form 6)) L594 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L600 ++ ([] : List (Form 6)) = L600 from rfl, show L594 ++ ([] : List (Form 6)) = L594 from rfl] at hh
  rw [i341 h, i346 h] at hh
  linarith

theorem row161 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    (1 : ℝ) * (CF Γ p).H L251 + (-1 : ℝ) * (CF Γ p).H L88 = 0 := by
  have hh : (CF Γ p).H (L90 ++ L18) = (CF Γ p).H (L23 ++ L18) :=
    Conf.H_copy_eqlaw (src := src2) (V := V2) (hv2 h) (by decide) L90 L18 L23 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L90 ++ L18 = L601 from rfl, show L23 ++ L18 = L596 from rfl] at hh
  rw [i343 h, i347 h] at hh
  linarith

theorem row162 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : HypZ Γ p) :
    (1 : ℝ) * (CF Γ p).H L253 + (-1 : ℝ) * (CF Γ p).H L51 = 0 := by
  have hh : (CF Γ p).H (L2 ++ L50) = (CF Γ p).H (L6 ++ L50) :=
    Conf.H_copy_eqlaw (src := src2) (V := V2) (hv2 h) (by decide) L2 L50 L6 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L2 ++ L50 = L602 from rfl, show L6 ++ L50 = L52 from rfl] at hh
  rw [i19 h, i348 h] at hh
  linarith

end EntropyBounds.GlueZ.Certs.C3BALL
