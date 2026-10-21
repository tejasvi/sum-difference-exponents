import EntropyBounds.TwoSet.Certs.R7A5.Ids0
import EntropyBounds.TwoSet.Certs.R7A5.Ids1
import EntropyBounds.TwoSet.Certs.R7A5.Ids2
import EntropyBounds.TwoSet.Certs.R7A5.Ids3
import EntropyBounds.TwoSet.Certs.R7A5.Ids4
import EntropyBounds.TwoSet.Certs.R7A5.Ids5
import EntropyBounds.TwoSet.Certs.R7A5.Ids6
import EntropyBounds.TwoSet.Certs.R7A5.Ids7
import EntropyBounds.TwoSet.Certs.R7A5.Ids8
import EntropyBounds.TwoSet.Certs.R7A5.Ids9
import EntropyBounds.TwoSet.Certs.R7A5.Ids10
import EntropyBounds.TwoSet.Certs.R7A5.Ids11
import EntropyBounds.TwoSet.Certs.R7A5.Ids12
import EntropyBounds.TwoSet.Certs.R7A5.Ids13
import EntropyBounds.TwoSet.Certs.R7A5.Ids14
import EntropyBounds.TwoSet.Certs.R7A5.Ids15
import EntropyBounds.TwoSet.Certs.R7A5.Ids16
import EntropyBounds.TwoSet.Certs.R7A5.Ids17
import EntropyBounds.TwoSet.Certs.R7A5.Ids18
import EntropyBounds.TwoSet.Certs.R7A5.Ids19
import EntropyBounds.TwoSet.Certs.R7A5.Ids20
import EntropyBounds.TwoSet.Certs.R7A5.Ids21
import EntropyBounds.TwoSet.Certs.R7A5.Ids22
import EntropyBounds.TwoSet.Certs.R7A5.Ids23
import EntropyBounds.TwoSet.Certs.R7A5.Ids24
import EntropyBounds.TwoSet.Certs.R7A5.Ids25
import EntropyBounds.TwoSet.Certs.R7A5.Ids26
import EntropyBounds.TwoSet.Certs.R7A5.Ids27
import EntropyBounds.TwoSet.Certs.R7A5.Ids28
import EntropyBounds.TwoSet.Certs.R7A5.Ids29
import EntropyBounds.TwoSet.Certs.R7A5.Ids30
import EntropyBounds.TwoSet.Certs.R7A5.Ids31
import EntropyBounds.TwoSet.Certs.R7A5.Ids32
import EntropyBounds.TwoSet.Certs.R7A5.Ids33
import EntropyBounds.TwoSet.Certs.R7A5.Ids34
import EntropyBounds.TwoSet.Certs.R7A5.Ids35
import EntropyBounds.TwoSet.Certs.R7A5.Ids36
import EntropyBounds.TwoSet.Certs.R7A5.Ids37
import EntropyBounds.TwoSet.Certs.R7A5.Ids38
import EntropyBounds.TwoSet.Certs.R7A5.Ids39
import EntropyBounds.TwoSet.Certs.R7A5.Ids40
import EntropyBounds.TwoSet.Certs.R7A5.Ids41
import EntropyBounds.TwoSet.Certs.R7A5.Ids42
import EntropyBounds.TwoSet.Certs.R7A5.Ids43
import EntropyBounds.TwoSet.Certs.R7A5.Ids44
import EntropyBounds.TwoSet.Certs.R7A5.Ids45
import EntropyBounds.TwoSet.Certs.R7A5.Ids46
import EntropyBounds.TwoSet.Certs.R7A5.Ids47
import EntropyBounds.Iid.NonShannon
import EntropyBounds.TwoSet.Common
import EntropyBounds.TwoSet.Mirror

set_option linter.unusedVariables false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open Finset Pointwise

namespace EntropyBounds.TwoSet.Certs.R7A5

open SumsDifferences SumsDifferences.NonShannon EntropyBounds.Iid EntropyBounds.TwoSet SumsDifferences.CoupledForms

theorem row3450 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2135 + (-1 : ℝ) * HLm Γ 5 L155 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L156 L12453 (by decide)
  rw [i7835 hinj, i50 hinj] at h
  linarith

theorem row3451 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2306 + (-1 : ℝ) * HLm Γ 5 L1280 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L1280 L12078 (by decide)
  rw [i7488 hinj] at h
  linarith

theorem row3452 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2454 + (-1 : ℝ) * HLm Γ 5 L2145 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L12455 L12454 (by decide)
  rw [i7836 hinj, i7837 hinj] at h
  linarith

theorem row3453 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12456 + (-1 : ℝ) * HLm Γ 5 L2284 = 0 := by
  have h := HLm_permB (Γ := Γ) ![3, 1, 2, 0, 4] ![3, 1, 2, 0, 4] (by decide) L2285 L12456 (by decide)
  rw [i1260 hinj] at h
  linarith

theorem row3454 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12457 + (-1 : ℝ) * HLm Γ 5 L7447 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L7448 L12458 (by decide)
  rw [i7838 hinj, i4409 hinj] at h
  linarith

theorem row3455 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2147 + (-1 : ℝ) * HLm Γ 5 L7684 = 0 := by
  have h := HLm_permB (Γ := Γ) ![3, 1, 2, 0, 4] ![3, 1, 2, 0, 4] (by decide) L7685 L12459 (by decide)
  rw [i7839 hinj, i4545 hinj] at h
  linarith

theorem row3456 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12456 + (-1 : ℝ) * HLm Γ 5 L2147 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L2148 L12460 (by decide)
  rw [i7840 hinj, i1177 hinj] at h
  linarith

theorem row3457 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2147 + (-1 : ℝ) * HLm Γ 5 L972 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L973 L2148 (by decide)
  rw [i1177 hinj, i450 hinj] at h
  linarith

theorem row3458 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12457 + (-1 : ℝ) * HLm Γ 5 L2147 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 2, 4, 3] ![0, 1, 2, 4, 3] (by decide) L2148 L12461 (by decide)
  rw [i7841 hinj, i1177 hinj] at h
  linarith

theorem row3459 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2151 + (-1 : ℝ) * HLm Γ 5 L2404 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L12463 L12462 (by decide)
  rw [i7842 hinj, i7843 hinj] at h
  linarith

theorem row3460 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L7925 + (-1 : ℝ) * HLm Γ 5 L2157 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L12464 L7926 (by decide)
  rw [i4674 hinj, i7844 hinj] at h
  linarith

theorem row3461 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2971 + (-1 : ℝ) * HLm Γ 5 L2157 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L12464 L2972 (by decide)
  rw [i1694 hinj, i7844 hinj] at h
  linarith

theorem row3462 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L1041 + (-1 : ℝ) * HLm Γ 5 L2158 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 3, 2, 1, 4] ![0, 3, 2, 1, 4] (by decide) L12466 L12465 (by decide)
  rw [i7845 hinj, i7846 hinj] at h
  linarith

theorem row3463 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L6790 + (-1 : ℝ) * HLm Γ 5 L3161 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 4, 2, 3, 1] ![0, 4, 2, 3, 1] (by decide) L3161 L6790 (by decide)
  linarith

theorem row3464 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2160 + (-1 : ℝ) * HLm Γ 5 L3161 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L3161 L2161 (by decide)
  rw [i1183 hinj] at h
  linarith

theorem row3465 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11322 + (-1 : ℝ) * HLm Γ 5 L12467 = 0 := by
  have h := HLm_permB (Γ := Γ) ![4, 0, 2, 3, 1] ![1, 4, 2, 3, 0] (by decide) L12468 L11323 (by decide)
  rw [i6936 hinj, i7847 hinj] at h
  linarith

theorem row3466 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12467 + (-1 : ℝ) * HLm Γ 5 L431 = 0 := by
  have h := HLm_permB (Γ := Γ) ![3, 1, 2, 0, 4] ![3, 1, 2, 0, 4] (by decide) L432 L12468 (by decide)
  rw [i7847 hinj, i176 hinj] at h
  linarith

theorem row3467 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2163 + (-1 : ℝ) * HLm Γ 5 L2244 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L2245 L12469 (by decide)
  rw [i7848 hinj, i1234 hinj] at h
  linarith

theorem row3468 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2165 + (-1 : ℝ) * HLm Γ 5 L2345 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L2345 L2166 (by decide)
  rw [i1186 hinj] at h
  linarith

theorem row3469 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2168 + (-1 : ℝ) * HLm Γ 5 L2321 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L12471 L12470 (by decide)
  rw [i7849 hinj, i7850 hinj] at h
  linarith

theorem row3470 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L644 + (-1 : ℝ) * HLm Γ 5 L8977 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 4, 2] ![0, 1, 4, 2, 3] (by decide) L12472 L12026 (by decide)
  rw [i7440 hinj, i7851 hinj] at h
  linarith

theorem row3471 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2585 + (-1 : ℝ) * HLm Γ 5 L8991 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 4, 2] ![0, 1, 4, 2, 3] (by decide) L12474 L12473 (by decide)
  rw [i7852 hinj, i7853 hinj] at h
  linarith

theorem row3472 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L8378 + (-1 : ℝ) * HLm Γ 5 L12476 = 0 := by
  have h := HLm_permB (Γ := Γ) ![3, 1, 2, 0, 4] ![3, 1, 2, 0, 4] (by decide) L12477 L12475 (by decide)
  rw [i7854 hinj, i7855 hinj] at h
  linarith

theorem row3473 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L338 + (-1 : ℝ) * HLm Γ 5 L2189 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 3, 2, 1, 4] ![0, 3, 2, 1, 4] (by decide) L12479 L12478 (by decide)
  rw [i7856 hinj, i7857 hinj] at h
  linarith

theorem row3474 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2585 + (-1 : ℝ) * HLm Γ 5 L2189 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L12479 L12480 (by decide)
  rw [i7858 hinj, i7857 hinj] at h
  linarith

theorem row3475 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2189 + (-1 : ℝ) * HLm Γ 5 L12476 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L12477 L12479 (by decide)
  rw [i7857 hinj, i7855 hinj] at h
  linarith

theorem row3476 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11417 + (-1 : ℝ) * HLm Γ 5 L12481 = 0 := by
  have h := HLm_permB (Γ := Γ) ![2, 1, 0, 3, 4] ![2, 1, 0, 3, 4] (by decide) L12482 L11417 (by decide)
  rw [i7859 hinj] at h
  linarith

theorem row3477 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12483 + (-1 : ℝ) * HLm Γ 5 L2206 = 0 := by
  have h := HLm_permB (Γ := Γ) ![2, 1, 0, 3, 4] ![2, 1, 0, 3, 4] (by decide) L2206 L12484 (by decide)
  rw [i7860 hinj] at h
  linarith

theorem row3478 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L7795 + (-1 : ℝ) * HLm Γ 5 L552 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 4, 1, 3, 2] ![0, 2, 4, 3, 1] (by decide) L552 L7795 (by decide)
  linarith

theorem row3479 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L550 + (-1 : ℝ) * HLm Γ 5 L12481 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 4, 2] ![1, 0, 4, 2, 3] (by decide) L12482 L550 (by decide)
  rw [i7859 hinj] at h
  linarith

theorem row3480 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12483 + (-1 : ℝ) * HLm Γ 5 L550 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L550 L12485 (by decide)
  rw [i7861 hinj] at h
  linarith

theorem row3481 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L778 + (-1 : ℝ) * HLm Γ 5 L2193 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L12487 L12486 (by decide)
  rw [i7862 hinj, i7863 hinj] at h
  linarith

theorem row3482 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L683 + (-1 : ℝ) * HLm Γ 5 L2197 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L12489 L12488 (by decide)
  rw [i7864 hinj, i7865 hinj] at h
  linarith

theorem row3483 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2202 + (-1 : ℝ) * HLm Γ 5 L2522 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L2523 L2203 (by decide)
  rw [i1209 hinj, i1398 hinj] at h
  linarith

theorem row3484 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2518 + (-1 : ℝ) * HLm Γ 5 L2204 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L12491 L12490 (by decide)
  rw [i7866 hinj, i7867 hinj] at h
  linarith

theorem row3485 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L638 + (-1 : ℝ) * HLm Γ 5 L2502 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L12493 L12492 (by decide)
  rw [i7868 hinj, i7869 hinj] at h
  linarith

theorem row3486 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L638 + (-1 : ℝ) * HLm Γ 5 L11140 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 4, 2] ![0, 1, 4, 2, 3] (by decide) L12494 L12492 (by decide)
  rw [i7868 hinj, i7870 hinj] at h
  linarith

theorem row3487 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11238 + (-1 : ℝ) * HLm Γ 5 L2219 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 4, 3] ![1, 0, 2, 4, 3] (by decide) L12496 L12495 (by decide)
  rw [i7871 hinj, i7872 hinj] at h
  linarith

theorem row3488 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L1769 + (-1 : ℝ) * HLm Γ 5 L2219 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L12496 L12497 (by decide)
  rw [i7873 hinj, i7872 hinj] at h
  linarith

theorem row3489 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L1182 + (-1 : ℝ) * HLm Γ 5 L2219 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L12496 L12498 (by decide)
  rw [i7874 hinj, i7872 hinj] at h
  linarith

theorem row3490 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2223 + (-1 : ℝ) * HLm Γ 5 L2533 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L2534 L12499 (by decide)
  rw [i7875 hinj, i1406 hinj] at h
  linarith

theorem row3491 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L7336 + (-1 : ℝ) * HLm Γ 5 L12501 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 4, 2, 3, 1] ![0, 4, 2, 3, 1] (by decide) L12502 L12500 (by decide)
  rw [i7876 hinj, i7877 hinj] at h
  linarith

theorem row3492 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12501 + (-1 : ℝ) * HLm Γ 5 L2230 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L2231 L12502 (by decide)
  rw [i7877 hinj, i1226 hinj] at h
  linarith

theorem row3493 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2236 + (-1 : ℝ) * HLm Γ 5 L2567 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L2568 L2237 (by decide)
  rw [i1229 hinj, i1431 hinj] at h
  linarith

theorem row3494 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2563 + (-1 : ℝ) * HLm Γ 5 L2238 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L12504 L12503 (by decide)
  rw [i7878 hinj, i7879 hinj] at h
  linarith

theorem row3495 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L8364 + (-1 : ℝ) * HLm Γ 5 L2241 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 4, 3, 2] ![1, 0, 4, 3, 2] (by decide) L12506 L12505 (by decide)
  rw [i7880 hinj, i7881 hinj] at h
  linarith

theorem row3496 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2241 + (-1 : ℝ) * HLm Γ 5 L8984 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 4, 2] ![0, 1, 4, 2, 3] (by decide) L12508 L12507 (by decide)
  rw [i7882 hinj, i7883 hinj] at h
  linarith

theorem row3497 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L4832 + (-1 : ℝ) * HLm Γ 5 L2241 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 4, 2] ![0, 1, 4, 2, 3] (by decide) L12506 L12509 (by decide)
  rw [i7884 hinj, i7881 hinj] at h
  linarith

theorem row3498 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L4452 + (-1 : ℝ) * HLm Γ 5 L2241 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L12506 L12510 (by decide)
  rw [i7885 hinj, i7881 hinj] at h
  linarith

theorem row3499 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11317 + (-1 : ℝ) * HLm Γ 5 L1622 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 4, 2, 3, 1] ![0, 4, 2, 3, 1] (by decide) L12511 L11318 (by decide)
  rw [i6933 hinj, i7886 hinj] at h
  linarith

theorem row3500 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12512 + (-1 : ℝ) * HLm Γ 5 L7360 = 0 := by
  have h := HLm_permB (Γ := Γ) ![2, 1, 0, 3, 4] ![2, 1, 0, 3, 4] (by decide) L7360 L12513 (by decide)
  rw [i7887 hinj] at h
  linarith

theorem row3501 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12514 + (-1 : ℝ) * HLm Γ 5 L2348 = 0 := by
  have h := HLm_permB (Γ := Γ) ![3, 1, 2, 0, 4] ![3, 1, 2, 0, 4] (by decide) L2348 L12515 (by decide)
  rw [i7888 hinj] at h
  linarith

theorem row3502 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12516 + (-1 : ℝ) * HLm Γ 5 L11214 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L12518 L12517 (by decide)
  rw [i7889 hinj, i7890 hinj] at h
  linarith

theorem row3503 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L1215 + (-1 : ℝ) * HLm Γ 5 L11218 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L12520 L12519 (by decide)
  rw [i7891 hinj, i7892 hinj] at h
  linarith

theorem row3504 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12512 + (-1 : ℝ) * HLm Γ 5 L1215 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 4, 3] ![1, 0, 2, 4, 3] (by decide) L1215 L12512 (by decide)
  linarith

theorem row3505 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12514 + (-1 : ℝ) * HLm Γ 5 L1215 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L1215 L12514 (by decide)
  linarith

theorem row3506 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12516 + (-1 : ℝ) * HLm Γ 5 L1215 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 2, 4, 3] ![0, 1, 2, 4, 3] (by decide) L1215 L12516 (by decide)
  linarith

theorem row3507 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L9336 + (-1 : ℝ) * HLm Γ 5 L2250 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L12522 L12521 (by decide)
  rw [i7893 hinj, i7894 hinj] at h
  linarith

theorem row3508 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L6860 + (-1 : ℝ) * HLm Γ 5 L92 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 4, 2, 3, 1] ![0, 4, 2, 3, 1] (by decide) L3620 L12523 (by decide)
  rw [i7895 hinj, i2028 hinj] at h
  linarith

theorem row3509 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3413 + (-1 : ℝ) * HLm Γ 5 L2266 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L12525 L12524 (by decide)
  rw [i7896 hinj, i7897 hinj] at h
  linarith

theorem row3510 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L8644 + (-1 : ℝ) * HLm Γ 5 L2270 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L12527 L12526 (by decide)
  rw [i7898 hinj, i7899 hinj] at h
  linarith

theorem row3511 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2274 + (-1 : ℝ) * HLm Γ 5 L2597 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L2598 L12528 (by decide)
  rw [i7900 hinj, i1451 hinj] at h
  linarith

theorem row3512 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2594 + (-1 : ℝ) * HLm Γ 5 L2276 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L12530 L12529 (by decide)
  rw [i7901 hinj, i7902 hinj] at h
  linarith

theorem row3513 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L9283 + (-1 : ℝ) * HLm Γ 5 L12532 = 0 := by
  have h := HLm_permB (Γ := Γ) ![3, 1, 2, 0, 4] ![3, 1, 2, 0, 4] (by decide) L12533 L12531 (by decide)
  rw [i7903 hinj, i7904 hinj] at h
  linarith

theorem row3514 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L7854 + (-1 : ℝ) * HLm Γ 5 L2278 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L12535 L12534 (by decide)
  rw [i7905 hinj, i7906 hinj] at h
  linarith

theorem row3515 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12532 + (-1 : ℝ) * HLm Γ 5 L2278 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 4, 3] ![1, 0, 2, 4, 3] (by decide) L12535 L12533 (by decide)
  rw [i7904 hinj, i7906 hinj] at h
  linarith

theorem row3516 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12536 + (-1 : ℝ) * HLm Γ 5 L8227 = 0 := by
  have h := HLm_permB (Γ := Γ) ![2, 1, 0, 3, 4] ![2, 1, 0, 3, 4] (by decide) L8227 L12537 (by decide)
  rw [i7907 hinj] at h
  linarith

theorem row3517 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L7660 + (-1 : ℝ) * HLm Γ 5 L12539 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 3, 2, 1, 4] ![0, 3, 2, 1, 4] (by decide) L12540 L12538 (by decide)
  rw [i7908 hinj, i7909 hinj] at h
  linarith

theorem row3518 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L714 + (-1 : ℝ) * HLm Γ 5 L12536 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 4, 2] ![1, 0, 4, 2, 3] (by decide) L12542 L12541 (by decide)
  rw [i7910 hinj, i7911 hinj] at h
  linarith

theorem row3519 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3107 + (-1 : ℝ) * HLm Γ 5 L714 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L714 L3107 (by decide)
  linarith

theorem row3520 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L714 + (-1 : ℝ) * HLm Γ 5 L12539 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 4, 2] ![0, 1, 4, 2, 3] (by decide) L12540 L12541 (by decide)
  rw [i7910 hinj, i7909 hinj] at h
  linarith

theorem row3521 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L553 + (-1 : ℝ) * HLm Γ 5 L2288 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L12544 L12543 (by decide)
  rw [i7912 hinj, i7913 hinj] at h
  linarith

theorem row3522 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2288 + (-1 : ℝ) * HLm Γ 5 L2492 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L12546 L12545 (by decide)
  rw [i7914 hinj, i7915 hinj] at h
  linarith

theorem row3523 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L8680 + (-1 : ℝ) * HLm Γ 5 L2303 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L12548 L12547 (by decide)
  rw [i7916 hinj, i7917 hinj] at h
  linarith

theorem row3524 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L8251 + (-1 : ℝ) * HLm Γ 5 L2303 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L12548 L12549 (by decide)
  rw [i7918 hinj, i7917 hinj] at h
  linarith

theorem row3525 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3823 + (-1 : ℝ) * HLm Γ 5 L12551 = 0 := by
  have h := HLm_permB (Γ := Γ) ![4, 1, 2, 3, 0] ![4, 1, 2, 3, 0] (by decide) L12552 L12550 (by decide)
  rw [i7919 hinj, i7920 hinj] at h
  linarith

theorem row3526 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2308 + (-1 : ℝ) * HLm Γ 5 L4642 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 3, 2, 1, 4] ![0, 3, 2, 1, 4] (by decide) L4643 L12553 (by decide)
  rw [i7921 hinj, i2608 hinj] at h
  linarith

theorem row3527 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12551 + (-1 : ℝ) * HLm Γ 5 L2308 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L2309 L12554 (by decide)
  rw [i7922 hinj, i1273 hinj] at h
  linarith

theorem row3528 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2308 + (-1 : ℝ) * HLm Γ 5 L2666 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L2667 L12555 (by decide)
  rw [i7923 hinj, i1498 hinj] at h
  linarith

theorem row3529 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11176 + (-1 : ℝ) * HLm Γ 5 L12557 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 3, 2, 1, 4] ![0, 3, 2, 1, 4] (by decide) L12558 L12556 (by decide)
  rw [i7924 hinj, i7925 hinj] at h
  linarith

theorem row3530 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12557 + (-1 : ℝ) * HLm Γ 5 L2310 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 2, 4, 3] ![0, 1, 2, 4, 3] (by decide) L12559 L12558 (by decide)
  rw [i7925 hinj, i7926 hinj] at h
  linarith

theorem row3531 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3521 + (-1 : ℝ) * HLm Γ 5 L12561 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L12562 L12560 (by decide)
  rw [i7927 hinj, i7928 hinj] at h
  linarith

theorem row3532 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12561 + (-1 : ℝ) * HLm Γ 5 L2312 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L2313 L12562 (by decide)
  rw [i7928 hinj, i1275 hinj] at h
  linarith

theorem row3533 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L4811 + (-1 : ℝ) * HLm Γ 5 L2315 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 4, 2, 3, 1] ![0, 4, 2, 3, 1] (by decide) L2316 L12563 (by decide)
  rw [i7929 hinj, i1276 hinj] at h
  linarith

theorem row3534 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2318 + (-1 : ℝ) * HLm Γ 5 L776 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L2660 L12564 (by decide)
  rw [i7930 hinj, i1494 hinj] at h
  linarith

theorem row3535 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2329 + (-1 : ℝ) * HLm Γ 5 L3535 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 3, 2, 1, 4] ![0, 3, 2, 1, 4] (by decide) L12566 L12565 (by decide)
  rw [i7931 hinj, i7932 hinj] at h
  linarith

theorem row3536 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2329 + (-1 : ℝ) * HLm Γ 5 L8929 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L8930 L4858 (by decide)
  rw [i2735 hinj, i5273 hinj] at h
  linarith

theorem row3537 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2681 + (-1 : ℝ) * HLm Γ 5 L2334 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L12568 L12567 (by decide)
  rw [i7933 hinj, i7934 hinj] at h
  linarith

theorem row3538 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L1637 + (-1 : ℝ) * HLm Γ 5 L2338 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L11859 L11858 (by decide)
  rw [i7287 hinj, i7288 hinj] at h
  linarith

theorem row3539 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2601 + (-1 : ℝ) * HLm Γ 5 L2346 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L12569 L8439 (by decide)
  rw [i4974 hinj, i7935 hinj] at h
  linarith

theorem row3540 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L5105 + (-1 : ℝ) * HLm Γ 5 L3337 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 4, 2, 3, 1] ![0, 4, 2, 3, 1] (by decide) L12571 L12570 (by decide)
  rw [i7936 hinj, i7937 hinj] at h
  linarith

theorem row3541 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L5106 + (-1 : ℝ) * HLm Γ 5 L2352 = 0 := by
  have h := HLm_permB (Γ := Γ) ![4, 1, 2, 3, 0] ![4, 1, 2, 3, 0] (by decide) L2352 L12572 (by decide)
  rw [i7938 hinj] at h
  linarith

theorem row3542 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3337 + (-1 : ℝ) * HLm Γ 5 L2352 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L2352 L12571 (by decide)
  rw [i7937 hinj] at h
  linarith

theorem row3543 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2358 + (-1 : ℝ) * HLm Γ 5 L2718 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L2719 L12573 (by decide)
  rw [i7939 hinj, i1533 hinj] at h
  linarith

theorem row3544 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2714 + (-1 : ℝ) * HLm Γ 5 L2360 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L12575 L12574 (by decide)
  rw [i7940 hinj, i7941 hinj] at h
  linarith

theorem row3545 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2364 + (-1 : ℝ) * HLm Γ 5 L2733 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L2734 L12576 (by decide)
  rw [i7942 hinj, i1541 hinj] at h
  linarith

theorem row3546 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2367 + (-1 : ℝ) * HLm Γ 5 L2635 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L2636 L12577 (by decide)
  rw [i7943 hinj, i1478 hinj] at h
  linarith

theorem row3547 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2370 + (-1 : ℝ) * HLm Γ 5 L2632 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L12579 L12578 (by decide)
  rw [i7944 hinj, i7945 hinj] at h
  linarith

theorem row3548 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12580 + (-1 : ℝ) * HLm Γ 5 L4050 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 4, 2] ![1, 0, 4, 2, 3] (by decide) L4051 L12581 (by decide)
  rw [i7946 hinj, i2260 hinj] at h
  linarith

theorem row3549 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3003 + (-1 : ℝ) * HLm Γ 5 L12583 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 3, 2, 1, 4] ![0, 3, 2, 1, 4] (by decide) L12584 L12582 (by decide)
  rw [i7947 hinj, i7948 hinj] at h
  linarith

theorem row3550 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2672 + (-1 : ℝ) * HLm Γ 5 L12583 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L12584 L12585 (by decide)
  rw [i7949 hinj, i7948 hinj] at h
  linarith

theorem row3551 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12580 + (-1 : ℝ) * HLm Γ 5 L2372 = 0 := by
  have h := HLm_permB (Γ := Γ) ![2, 1, 0, 3, 4] ![2, 1, 0, 3, 4] (by decide) L2373 L12586 (by decide)
  rw [i7950 hinj, i1307 hinj] at h
  linarith

theorem row3552 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2372 + (-1 : ℝ) * HLm Γ 5 L12583 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L12584 L12587 (by decide)
  rw [i7951 hinj, i7948 hinj] at h
  linarith

theorem row3553 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L8783 + (-1 : ℝ) * HLm Γ 5 L8336 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L12589 L12588 (by decide)
  rw [i7952 hinj, i7953 hinj] at h
  linarith

theorem row3554 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2376 + (-1 : ℝ) * HLm Γ 5 L8783 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L12591 L12590 (by decide)
  rw [i7954 hinj, i7955 hinj] at h
  linarith

theorem row3555 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3001 + (-1 : ℝ) * HLm Γ 5 L12592 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 3, 2, 1, 4] ![0, 3, 2, 1, 4] (by decide) L12592 L3002 (by decide)
  rw [i1710 hinj] at h
  linarith

theorem row3556 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L439 + (-1 : ℝ) * HLm Γ 5 L2378 = 0 := by
  have h := HLm_permB (Γ := Γ) ![3, 1, 2, 0, 4] ![3, 1, 2, 0, 4] (by decide) L2378 L440 (by decide)
  rw [i180 hinj] at h
  linarith

theorem row3557 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12592 + (-1 : ℝ) * HLm Γ 5 L2378 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L2378 L12592 (by decide)
  linarith

theorem row3558 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L895 + (-1 : ℝ) * HLm Γ 5 L2745 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L12594 L12593 (by decide)
  rw [i7956 hinj, i7957 hinj] at h
  linarith

theorem row3559 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11240 + (-1 : ℝ) * HLm Γ 5 L895 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 4, 3, 2] ![0, 1, 4, 3, 2] (by decide) L12593 L11241 (by decide)
  rw [i6887 hinj, i7956 hinj] at h
  linarith

theorem row3560 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L1778 + (-1 : ℝ) * HLm Γ 5 L1325 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L12182 L12595 (by decide)
  rw [i7958 hinj, i7585 hinj] at h
  linarith

theorem row3561 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L8682 + (-1 : ℝ) * HLm Γ 5 L2398 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L2399 L8683 (by decide)
  rw [i5123 hinj, i1320 hinj] at h
  linarith

theorem row3562 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12596 + (-1 : ℝ) * HLm Γ 5 L7147 = 0 := by
  have h := HLm_permB (Γ := Γ) ![3, 1, 2, 0, 4] ![3, 1, 2, 0, 4] (by decide) L12598 L12597 (by decide)
  rw [i7959 hinj, i7960 hinj] at h
  linarith

theorem row3563 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12599 + (-1 : ℝ) * HLm Γ 5 L7381 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L12601 L12600 (by decide)
  rw [i7961 hinj, i7962 hinj] at h
  linarith

theorem row3564 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2400 + (-1 : ℝ) * HLm Γ 5 L6862 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 3, 2, 1, 4] ![0, 3, 2, 1, 4] (by decide) L6863 L12602 (by decide)
  rw [i7963 hinj, i4083 hinj] at h
  linarith

theorem row3565 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12596 + (-1 : ℝ) * HLm Γ 5 L2400 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L12604 L12603 (by decide)
  rw [i7964 hinj, i7965 hinj] at h
  linarith

theorem row3566 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12599 + (-1 : ℝ) * HLm Γ 5 L2400 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 2, 4, 3] ![0, 1, 2, 4, 3] (by decide) L12604 L12605 (by decide)
  rw [i7966 hinj, i7965 hinj] at h
  linarith

theorem row3567 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2402 + (-1 : ℝ) * HLm Γ 5 L9210 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L12607 L12606 (by decide)
  rw [i7967 hinj, i7968 hinj] at h
  linarith

theorem row3568 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L8087 + (-1 : ℝ) * HLm Γ 5 L595 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L595 L8087 (by decide)
  linarith

theorem row3569 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L7177 + (-1 : ℝ) * HLm Γ 5 L595 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 4, 2] ![0, 1, 4, 2, 3] (by decide) L595 L7177 (by decide)
  linarith

theorem row3570 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L8580 + (-1 : ℝ) * HLm Γ 5 L12609 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L12610 L12608 (by decide)
  rw [i7969 hinj, i7970 hinj] at h
  linarith

theorem row3571 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L981 + (-1 : ℝ) * HLm Γ 5 L12609 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L12610 L12153 (by decide)
  rw [i7557 hinj, i7970 hinj] at h
  linarith

theorem row3572 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L9478 + (-1 : ℝ) * HLm Γ 5 L989 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 4, 2] ![1, 0, 4, 2, 3] (by decide) L1300 L12611 (by decide)
  rw [i7971 hinj, i639 hinj] at h
  linarith

theorem row3573 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2728 + (-1 : ℝ) * HLm Γ 5 L1007 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L12161 L2729 (by decide)
  rw [i1538 hinj, i7565 hinj] at h
  linarith

theorem row3574 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L7748 + (-1 : ℝ) * HLm Γ 5 L1029 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 4, 3] ![1, 0, 2, 4, 3] (by decide) L12167 L12612 (by decide)
  rw [i7972 hinj, i7571 hinj] at h
  linarith

theorem row3575 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2407 + (-1 : ℝ) * HLm Γ 5 L7949 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 4, 2] ![0, 1, 4, 2, 3] (by decide) L7950 L2408 (by decide)
  rw [i1325 hinj, i4688 hinj] at h
  linarith

theorem row3576 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3292 + (-1 : ℝ) * HLm Γ 5 L2407 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L2408 L4338 (by decide)
  rw [i2433 hinj, i1325 hinj] at h
  linarith

theorem row3577 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2409 + (-1 : ℝ) * HLm Γ 5 L8989 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 4, 2] ![0, 1, 4, 2, 3] (by decide) L8990 L4820 (by decide)
  rw [i2711 hinj, i5309 hinj] at h
  linarith

theorem row3578 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2411 + (-1 : ℝ) * HLm Γ 5 L1767 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L12213 L12613 (by decide)
  rw [i7973 hinj, i7614 hinj] at h
  linarith

theorem row3579 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2413 + (-1 : ℝ) * HLm Γ 5 L7015 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 4, 2] ![0, 1, 4, 2, 3] (by decide) L7016 L2414 (by decide)
  rw [i1328 hinj, i4165 hinj] at h
  linarith

theorem row3580 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L6920 + (-1 : ℝ) * HLm Γ 5 L372 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L12615 L12614 (by decide)
  rw [i7974 hinj, i7975 hinj] at h
  linarith

theorem row3581 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L8382 + (-1 : ℝ) * HLm Γ 5 L2720 = 0 := by
  have h := HLm_permB (Γ := Γ) ![4, 1, 2, 3, 0] ![4, 1, 2, 3, 0] (by decide) L12617 L12616 (by decide)
  rw [i7976 hinj, i7977 hinj] at h
  linarith

theorem row3582 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2720 + (-1 : ℝ) * HLm Γ 5 L1069 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L12196 L12617 (by decide)
  rw [i7977 hinj, i7598 hinj] at h
  linarith

theorem row3583 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2417 + (-1 : ℝ) * HLm Γ 5 L3644 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 4, 2] ![1, 0, 4, 2, 3] (by decide) L3645 L12618 (by decide)
  rw [i7978 hinj, i2041 hinj] at h
  linarith

theorem row3584 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2417 + (-1 : ℝ) * HLm Γ 5 L3379 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L4402 L12618 (by decide)
  rw [i7978 hinj, i2468 hinj] at h
  linarith

theorem row3585 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2421 + (-1 : ℝ) * HLm Γ 5 L9855 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L9856 L12619 (by decide)
  rw [i7979 hinj, i5865 hinj] at h
  linarith

theorem row3586 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L1083 + (-1 : ℝ) * HLm Γ 5 L8192 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 4, 3, 2] ![1, 0, 4, 3, 2] (by decide) L12620 L12198 (by decide)
  rw [i7600 hinj, i7980 hinj] at h
  linarith

theorem row3587 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L1569 + (-1 : ℝ) * HLm Γ 5 L2428 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L12622 L12621 (by decide)
  rw [i7981 hinj, i7982 hinj] at h
  linarith

theorem row3588 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L1123 + (-1 : ℝ) * HLm Γ 5 L2431 = 0 := by
  have h := HLm_permB (Γ := Γ) ![2, 1, 0, 3, 4] ![2, 1, 0, 3, 4] (by decide) L2432 L3077 (by decide)
  rw [i1750 hinj, i1339 hinj] at h
  linarith

theorem row3589 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2431 + (-1 : ℝ) * HLm Γ 5 L2551 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L2552 L12623 (by decide)
  rw [i7983 hinj, i1419 hinj] at h
  linarith

theorem row3590 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2433 + (-1 : ℝ) * HLm Γ 5 L1093 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L12625 L12624 (by decide)
  rw [i7984 hinj, i7985 hinj] at h
  linarith

theorem row3591 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L9318 + (-1 : ℝ) * HLm Γ 5 L2438 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L12627 L12626 (by decide)
  rw [i7986 hinj, i7987 hinj] at h
  linarith

theorem row3592 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L1129 + (-1 : ℝ) * HLm Γ 5 L7583 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 4, 2] ![1, 0, 4, 2, 3] (by decide) L12629 L12628 (by decide)
  rw [i7988 hinj, i7989 hinj] at h
  linarith

theorem row3593 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L7071 + (-1 : ℝ) * HLm Γ 5 L1129 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L12631 L12630 (by decide)
  rw [i7990 hinj, i7991 hinj] at h
  linarith

theorem row3594 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L1141 + (-1 : ℝ) * HLm Γ 5 L11381 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L12633 L12632 (by decide)
  rw [i7992 hinj, i7993 hinj] at h
  linarith

theorem row3595 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2444 + (-1 : ℝ) * HLm Γ 5 L2743 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L2744 L12634 (by decide)
  rw [i7994 hinj, i1547 hinj] at h
  linarith

theorem row3596 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2740 + (-1 : ℝ) * HLm Γ 5 L2446 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L12636 L12635 (by decide)
  rw [i7995 hinj, i7996 hinj] at h
  linarith

theorem row3597 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2450 + (-1 : ℝ) * HLm Γ 5 L2695 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L2696 L12637 (by decide)
  rw [i7997 hinj, i1518 hinj] at h
  linarith

theorem row3598 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2692 + (-1 : ℝ) * HLm Γ 5 L2452 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L12639 L12638 (by decide)
  rw [i7998 hinj, i7999 hinj] at h
  linarith

theorem row3599 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2456 + (-1 : ℝ) * HLm Γ 5 L2747 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L12641 L12640 (by decide)
  rw [i8000 hinj, i8001 hinj] at h
  linarith

end EntropyBounds.TwoSet.Certs.R7A5
