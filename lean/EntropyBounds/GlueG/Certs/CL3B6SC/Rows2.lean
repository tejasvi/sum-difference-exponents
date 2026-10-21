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

theorem row300 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    (1 : ℝ) * (CF Γ p).H L198 + (-1 : ℝ) * (CF Γ p).H L1048 = 0 := by
  have hh : (C2 Γ p).H (L1374 ++ ([] : List (Form 6))) = (C2 Γ p).H (L1372 ++ ([] : List (Form 6))) :=
    Conf.H_copy_eqlaw (src := src1) (V := V1) (hv1 h) (by decide) L1374 ([] : List (Form 6)) L1372 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L1374 ++ ([] : List (Form 6)) = L1374 from rfl, show L1372 ++ ([] : List (Form 6)) = L1372 from rfl] at hh
  rw [← lift2 h L1372 (by decide), ← lift2 h L1374 (by decide)] at hh
  rw [i924 h, i925 h] at hh
  linarith

theorem row301 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    (1 : ℝ) * (CF Γ p).H L127 + (-1 : ℝ) * (CF Γ p).H L152 = 0 := by
  have hh : (C2 Γ p).H (L1374 ++ L23) = (C2 Γ p).H (L1372 ++ L23) :=
    Conf.H_copy_eqlaw (src := src1) (V := V1) (hv1 h) (by decide) L1374 L23 L1372 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L1374 ++ L23 = L1376 from rfl, show L1372 ++ L23 = L1378 from rfl] at hh
  rw [← lift2 h L1378 (by decide), ← lift2 h L1376 (by decide)] at hh
  rw [i927 h, i926 h] at hh
  linarith

theorem row302 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    (1 : ℝ) * (CF Γ p).H L373 + (-1 : ℝ) * (CF Γ p).H L92 = 0 := by
  have hh : (C2 Γ p).H (L29 ++ L23) = (C2 Γ p).H (L39 ++ L23) :=
    Conf.H_copy_eqlaw (src := src1) (V := V1) (hv1 h) (by decide) L29 L23 L39 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L29 ++ L23 = L1380 from rfl, show L39 ++ L23 = L1381 from rfl] at hh
  rw [← lift2 h L1381 (by decide), ← lift2 h L1380 (by decide)] at hh
  rw [i929 h, i928 h] at hh
  linarith

theorem row303 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    (1 : ℝ) * (CF Γ p).H L446 + (-1 : ℝ) * (CF Γ p).H L143 = 0 := by
  have hh : (C2 Γ p).H (L1382 ++ ([] : List (Form 6))) = (C2 Γ p).H (L1383 ++ ([] : List (Form 6))) :=
    Conf.H_copy_eqlaw (src := src1) (V := V1) (hv1 h) (by decide) L1382 ([] : List (Form 6)) L1383 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L1382 ++ ([] : List (Form 6)) = L1382 from rfl, show L1383 ++ ([] : List (Form 6)) = L1383 from rfl] at hh
  rw [← lift2 h L1383 (by decide), ← lift2 h L1382 (by decide)] at hh
  rw [i931 h, i930 h] at hh
  linarith

theorem row304 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    (1 : ℝ) * (CF Γ p).H L375 + (-1 : ℝ) * (CF Γ p).H L94 = 0 := by
  have hh : (C2 Γ p).H (L26 ++ L89) = (C2 Γ p).H (L36 ++ L89) :=
    Conf.H_copy_eqlaw (src := src1) (V := V1) (hv1 h) (by decide) L26 L89 L36 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L26 ++ L89 = L1384 from rfl, show L36 ++ L89 = L95 from rfl] at hh
  rw [← lift2 h L95 (by decide), ← lift2 h L1384 (by decide)] at hh
  rw [i37 h, i932 h] at hh
  linarith

theorem row305 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    (1 : ℝ) * (CF Γ p).H L13 + (-1 : ℝ) * (CF Γ p).H L17 = 0 := by
  have hh : (CF Γ p).H (L14 ++ ([] : List (Form 6))) = (CF Γ p).H (L18 ++ ([] : List (Form 6))) :=
    Conf.H_copy_eqlaw (src := src2) (V := V2) (hv2 h) (by decide) L14 ([] : List (Form 6)) L18 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L14 ++ ([] : List (Form 6)) = L14 from rfl, show L18 ++ ([] : List (Form 6)) = L18 from rfl] at hh
  rw [i9 h, i7 h] at hh
  linarith

theorem row306 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    (1 : ℝ) * (CF Γ p).H L19 + (-1 : ℝ) * (CF Γ p).H L22 = 0 := by
  have hh : (CF Γ p).H (L19 ++ ([] : List (Form 6))) = (CF Γ p).H (L23 ++ ([] : List (Form 6))) :=
    Conf.H_copy_eqlaw (src := src2) (V := V2) (hv2 h) (by decide) L19 ([] : List (Form 6)) L23 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L19 ++ ([] : List (Form 6)) = L19 from rfl, show L23 ++ ([] : List (Form 6)) = L23 from rfl] at hh
  rw [i11 h] at hh
  linarith

theorem row307 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    (1 : ℝ) * (CF Γ p).H L320 + (-1 : ℝ) * (CF Γ p).H L273 = 0 := by
  have hh : (CF Γ p).H (L321 ++ ([] : List (Form 6))) = (CF Γ p).H (L274 ++ ([] : List (Form 6))) :=
    Conf.H_copy_eqlaw (src := src2) (V := V2) (hv2 h) (by decide) L321 ([] : List (Form 6)) L274 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L321 ++ ([] : List (Form 6)) = L321 from rfl, show L274 ++ ([] : List (Form 6)) = L274 from rfl] at hh
  rw [i110 h, i137 h] at hh
  linarith

theorem row308 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    (1 : ℝ) * (CF Γ p).H L32 + (-1 : ℝ) * (CF Γ p).H L39 = 0 := by
  have hh : (CF Γ p).H (L32 ++ ([] : List (Form 6))) = (CF Γ p).H (L39 ++ ([] : List (Form 6))) :=
    Conf.H_copy_eqlaw (src := src2) (V := V2) (hv2 h) (by decide) L32 ([] : List (Form 6)) L39 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L32 ++ ([] : List (Form 6)) = L32 from rfl, show L39 ++ ([] : List (Form 6)) = L39 from rfl] at hh
  linarith

theorem row309 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    (1 : ℝ) * (CF Γ p).H L208 + (-1 : ℝ) * (CF Γ p).H L1048 = 0 := by
  have hh : (CF Γ p).H (L1186 ++ ([] : List (Form 6))) = (CF Γ p).H (L1372 ++ ([] : List (Form 6))) :=
    Conf.H_copy_eqlaw (src := src2) (V := V2) (hv2 h) (by decide) L1186 ([] : List (Form 6)) L1372 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L1186 ++ ([] : List (Form 6)) = L1186 from rfl, show L1372 ++ ([] : List (Form 6)) = L1372 from rfl] at hh
  rw [i924 h, i757 h] at hh
  linarith

theorem row310 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    (1 : ℝ) * (CF Γ p).H L180 + (-1 : ℝ) * (CF Γ p).H L152 = 0 := by
  have hh : (CF Γ p).H (L1385 ++ ([] : List (Form 6))) = (CF Γ p).H (L1378 ++ ([] : List (Form 6))) :=
    Conf.H_copy_eqlaw (src := src2) (V := V2) (hv2 h) (by decide) L1385 ([] : List (Form 6)) L1378 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L1385 ++ ([] : List (Form 6)) = L1385 from rfl, show L1378 ++ ([] : List (Form 6)) = L1378 from rfl] at hh
  rw [i927 h, i933 h] at hh
  linarith

theorem row311 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    (1 : ℝ) * (CF Γ p).H L369 + (-1 : ℝ) * (CF Γ p).H L92 = 0 := by
  have hh : (CF Γ p).H (L1387 ++ ([] : List (Form 6))) = (CF Γ p).H (L1381 ++ ([] : List (Form 6))) :=
    Conf.H_copy_eqlaw (src := src2) (V := V2) (hv2 h) (by decide) L1387 ([] : List (Form 6)) L1381 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L1387 ++ ([] : List (Form 6)) = L1387 from rfl, show L1381 ++ ([] : List (Form 6)) = L1381 from rfl] at hh
  rw [i929 h, i934 h] at hh
  linarith

theorem row312 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    (1 : ℝ) * (CF Γ p).H L359 + (-1 : ℝ) * (CF Γ p).H L143 = 0 := by
  have hh : (CF Γ p).H (L32 ++ L36) = (CF Γ p).H (L39 ++ L36) :=
    Conf.H_copy_eqlaw (src := src2) (V := V2) (hv2 h) (by decide) L32 L36 L39 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L32 ++ L36 = L1388 from rfl, show L39 ++ L36 = L1383 from rfl] at hh
  rw [i931 h, i935 h] at hh
  linarith

theorem row313 (Γ : Finset (G × G)) (p : G × G → ℝ) (h : Hyp Γ p) :
    (1 : ℝ) * (CF Γ p).H L361 + (-1 : ℝ) * (CF Γ p).H L90 = 0 := by
  have hh : (CF Γ p).H (L19 ++ L89) = (CF Γ p).H (L23 ++ L89) :=
    Conf.H_copy_eqlaw (src := src2) (V := V2) (hv2 h) (by decide) L19 L89 L23 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L19 ++ L89 = L1389 from rfl, show L23 ++ L89 = L91 from rfl] at hh
  rw [i35 h, i936 h] at hh
  linarith

end EntropyBounds.GlueG.Certs.CL3B6SC
