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

theorem row300 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    (1 : ℝ) * (CF Γ p).H L238 + (-1 : ℝ) * (CF Γ p).H L1097 = 0 := by
  have hh : (C2 Γ p).H (L1425 ++ ([] : List (Form 6))) = (C2 Γ p).H (L1423 ++ ([] : List (Form 6))) :=
    Conf.H_copy_eqlaw (src := src1) (V := V1) (hv1 h) (by decide) L1425 ([] : List (Form 6)) L1423 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L1425 ++ ([] : List (Form 6)) = L1425 from rfl, show L1423 ++ ([] : List (Form 6)) = L1423 from rfl] at hh
  rw [← lift2 h L1423 (by decide), ← lift2 h L1425 (by decide)] at hh
  rw [i976 h, i977 h] at hh
  linarith

theorem row301 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    (1 : ℝ) * (CF Γ p).H L154 + (-1 : ℝ) * (CF Γ p).H L183 = 0 := by
  have hh : (C2 Γ p).H (L1425 ++ L23) = (C2 Γ p).H (L1423 ++ L23) :=
    Conf.H_copy_eqlaw (src := src1) (V := V1) (hv1 h) (by decide) L1425 L23 L1423 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L1425 ++ L23 = L1427 from rfl, show L1423 ++ L23 = L1429 from rfl] at hh
  rw [← lift2 h L1429 (by decide), ← lift2 h L1427 (by decide)] at hh
  rw [i979 h, i978 h] at hh
  linarith

theorem row302 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    (1 : ℝ) * (CF Γ p).H L415 + (-1 : ℝ) * (CF Γ p).H L109 = 0 := by
  have hh : (C2 Γ p).H (L31 ++ L23) = (C2 Γ p).H (L43 ++ L23) :=
    Conf.H_copy_eqlaw (src := src1) (V := V1) (hv1 h) (by decide) L31 L23 L43 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L31 ++ L23 = L1431 from rfl, show L43 ++ L23 = L1432 from rfl] at hh
  rw [← lift2 h L1432 (by decide), ← lift2 h L1431 (by decide)] at hh
  rw [i981 h, i980 h] at hh
  linarith

theorem row303 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    (1 : ℝ) * (CF Γ p).H L489 + (-1 : ℝ) * (CF Γ p).H L173 = 0 := by
  have hh : (C2 Γ p).H (L1433 ++ ([] : List (Form 6))) = (C2 Γ p).H (L1434 ++ ([] : List (Form 6))) :=
    Conf.H_copy_eqlaw (src := src1) (V := V1) (hv1 h) (by decide) L1433 ([] : List (Form 6)) L1434 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L1433 ++ ([] : List (Form 6)) = L1433 from rfl, show L1434 ++ ([] : List (Form 6)) = L1434 from rfl] at hh
  rw [← lift2 h L1434 (by decide), ← lift2 h L1433 (by decide)] at hh
  rw [i983 h, i982 h] at hh
  linarith

theorem row304 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    (1 : ℝ) * (CF Γ p).H L417 + (-1 : ℝ) * (CF Γ p).H L111 = 0 := by
  have hh : (C2 Γ p).H (L27 ++ L106) = (C2 Γ p).H (L39 ++ L106) :=
    Conf.H_copy_eqlaw (src := src1) (V := V1) (hv1 h) (by decide) L27 L106 L39 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L27 ++ L106 = L1435 from rfl, show L39 ++ L106 = L112 from rfl] at hh
  rw [← lift2 h L112 (by decide), ← lift2 h L1435 (by decide)] at hh
  rw [i55 h, i984 h] at hh
  linarith

theorem row305 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    (1 : ℝ) * (CF Γ p).H L12 + (-1 : ℝ) * (CF Γ p).H L16 = 0 := by
  have hh : (CF Γ p).H (L13 ++ ([] : List (Form 6))) = (CF Γ p).H (L17 ++ ([] : List (Form 6))) :=
    Conf.H_copy_eqlaw (src := src2) (V := V2) (hv2 h) (by decide) L13 ([] : List (Form 6)) L17 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L13 ++ ([] : List (Form 6)) = L13 from rfl, show L17 ++ ([] : List (Form 6)) = L17 from rfl] at hh
  rw [i9 h, i7 h] at hh
  linarith

theorem row306 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    (1 : ℝ) * (CF Γ p).H L18 + (-1 : ℝ) * (CF Γ p).H L22 = 0 := by
  have hh : (CF Γ p).H (L19 ++ ([] : List (Form 6))) = (CF Γ p).H (L23 ++ ([] : List (Form 6))) :=
    Conf.H_copy_eqlaw (src := src2) (V := V2) (hv2 h) (by decide) L19 ([] : List (Form 6)) L23 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L19 ++ ([] : List (Form 6)) = L19 from rfl, show L23 ++ ([] : List (Form 6)) = L23 from rfl] at hh
  rw [i12 h, i10 h] at hh
  linarith

theorem row307 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    (1 : ℝ) * (CF Γ p).H L362 + (-1 : ℝ) * (CF Γ p).H L314 = 0 := by
  have hh : (CF Γ p).H (L363 ++ ([] : List (Form 6))) = (CF Γ p).H (L315 ++ ([] : List (Form 6))) :=
    Conf.H_copy_eqlaw (src := src2) (V := V2) (hv2 h) (by decide) L363 ([] : List (Form 6)) L315 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L363 ++ ([] : List (Form 6)) = L363 from rfl, show L315 ++ ([] : List (Form 6)) = L315 from rfl] at hh
  rw [i152 h, i180 h] at hh
  linarith

theorem row308 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    (1 : ℝ) * (CF Γ p).H L34 + (-1 : ℝ) * (CF Γ p).H L42 = 0 := by
  have hh : (CF Γ p).H (L35 ++ ([] : List (Form 6))) = (CF Γ p).H (L43 ++ ([] : List (Form 6))) :=
    Conf.H_copy_eqlaw (src := src2) (V := V2) (hv2 h) (by decide) L35 ([] : List (Form 6)) L43 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L35 ++ ([] : List (Form 6)) = L35 from rfl, show L43 ++ ([] : List (Form 6)) = L43 from rfl] at hh
  rw [i22 h, i18 h] at hh
  linarith

theorem row309 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    (1 : ℝ) * (CF Γ p).H L248 + (-1 : ℝ) * (CF Γ p).H L1097 = 0 := by
  have hh : (CF Γ p).H (L1235 ++ ([] : List (Form 6))) = (CF Γ p).H (L1423 ++ ([] : List (Form 6))) :=
    Conf.H_copy_eqlaw (src := src2) (V := V2) (hv2 h) (by decide) L1235 ([] : List (Form 6)) L1423 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L1235 ++ ([] : List (Form 6)) = L1235 from rfl, show L1423 ++ ([] : List (Form 6)) = L1423 from rfl] at hh
  rw [i976 h, i807 h] at hh
  linarith

theorem row310 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    (1 : ℝ) * (CF Γ p).H L215 + (-1 : ℝ) * (CF Γ p).H L183 = 0 := by
  have hh : (CF Γ p).H (L1436 ++ ([] : List (Form 6))) = (CF Γ p).H (L1429 ++ ([] : List (Form 6))) :=
    Conf.H_copy_eqlaw (src := src2) (V := V2) (hv2 h) (by decide) L1436 ([] : List (Form 6)) L1429 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L1436 ++ ([] : List (Form 6)) = L1436 from rfl, show L1429 ++ ([] : List (Form 6)) = L1429 from rfl] at hh
  rw [i979 h, i985 h] at hh
  linarith

theorem row311 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    (1 : ℝ) * (CF Γ p).H L411 + (-1 : ℝ) * (CF Γ p).H L109 = 0 := by
  have hh : (CF Γ p).H (L1438 ++ ([] : List (Form 6))) = (CF Γ p).H (L1432 ++ ([] : List (Form 6))) :=
    Conf.H_copy_eqlaw (src := src2) (V := V2) (hv2 h) (by decide) L1438 ([] : List (Form 6)) L1432 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L1438 ++ ([] : List (Form 6)) = L1438 from rfl, show L1432 ++ ([] : List (Form 6)) = L1432 from rfl] at hh
  rw [i981 h, i986 h] at hh
  linarith

theorem row312 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    (1 : ℝ) * (CF Γ p).H L401 + (-1 : ℝ) * (CF Γ p).H L173 = 0 := by
  have hh : (CF Γ p).H (L35 ++ L39) = (CF Γ p).H (L43 ++ L39) :=
    Conf.H_copy_eqlaw (src := src2) (V := V2) (hv2 h) (by decide) L35 L39 L43 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L35 ++ L39 = L1439 from rfl, show L43 ++ L39 = L1434 from rfl] at hh
  rw [i983 h, i987 h] at hh
  linarith

theorem row313 (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (h : Hyp Γ p) :
    (1 : ℝ) * (CF Γ p).H L403 + (-1 : ℝ) * (CF Γ p).H L107 = 0 := by
  have hh : (CF Γ p).H (L19 ++ L106) = (CF Γ p).H (L23 ++ L106) :=
    Conf.H_copy_eqlaw (src := src2) (V := V2) (hv2 h) (by decide) L19 L106 L23 (by decide) (by decide)
      (by decide) (by decide)
  rw [show L19 ++ L106 = L1440 from rfl, show L23 ++ L106 = L108 from rfl] at hh
  rw [i53 h, i988 h] at hh
  linarith

end EntropyBounds.Glue.Certs.CL3B6SC
