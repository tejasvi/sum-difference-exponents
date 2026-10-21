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

theorem row4650 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11433 + (-1 : ℝ) * HLm Γ 5 L11481 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L11482 L14147 (by decide)
  rw [i9407 hinj, i7022 hinj] at h
  linarith

theorem row4651 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11437 + (-1 : ℝ) * HLm Γ 5 L3136 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L4126 L11438 (by decide)
  rw [i6999 hinj, i2303 hinj] at h
  linarith

theorem row4652 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11451 + (-1 : ℝ) * HLm Γ 5 L11507 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L11508 L11452 (by decide)
  rw [i7006 hinj, i7037 hinj] at h
  linarith

theorem row4653 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11453 + (-1 : ℝ) * HLm Γ 5 L11509 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L11510 L14148 (by decide)
  rw [i9408 hinj, i7038 hinj] at h
  linarith

theorem row4654 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11455 + (-1 : ℝ) * HLm Γ 5 L11511 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L11512 L14149 (by decide)
  rw [i9409 hinj, i7039 hinj] at h
  linarith

theorem row4655 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11457 + (-1 : ℝ) * HLm Γ 5 L11505 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L11506 L11458 (by decide)
  rw [i7009 hinj, i7036 hinj] at h
  linarith

theorem row4656 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11531 + (-1 : ℝ) * HLm Γ 5 L11463 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L14151 L14150 (by decide)
  rw [i9410 hinj, i9411 hinj] at h
  linarith

theorem row4657 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11467 + (-1 : ℝ) * HLm Γ 5 L11540 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L11541 L14152 (by decide)
  rw [i9412 hinj, i7054 hinj] at h
  linarith

theorem row4658 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11470 + (-1 : ℝ) * HLm Γ 5 L11536 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L14154 L14153 (by decide)
  rw [i9413 hinj, i9414 hinj] at h
  linarith

theorem row4659 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11479 + (-1 : ℝ) * HLm Γ 5 L11542 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L14155 L11480 (by decide)
  rw [i7021 hinj, i9415 hinj] at h
  linarith

theorem row4660 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11515 + (-1 : ℝ) * HLm Γ 5 L11525 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 4, 3] ![1, 0, 2, 4, 3] (by decide) L11526 L14156 (by decide)
  rw [i9416 hinj, i7046 hinj] at h
  linarith

theorem row4661 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11613 + (-1 : ℝ) * HLm Γ 5 L11515 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 4, 2] ![0, 1, 4, 2, 3] (by decide) L14157 L11614 (by decide)
  rw [i7097 hinj, i9417 hinj] at h
  linarith

theorem row4662 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11527 + (-1 : ℝ) * HLm Γ 5 L11519 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 4, 3] ![1, 0, 2, 4, 3] (by decide) L14159 L14158 (by decide)
  rw [i9418 hinj, i9419 hinj] at h
  linarith

theorem row4663 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11610 + (-1 : ℝ) * HLm Γ 5 L11519 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 4, 2] ![0, 1, 4, 2, 3] (by decide) L14159 L14160 (by decide)
  rw [i9420 hinj, i9419 hinj] at h
  linarith

theorem row4664 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11601 + (-1 : ℝ) * HLm Γ 5 L11705 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 4, 3] ![1, 0, 2, 4, 3] (by decide) L11706 L14161 (by decide)
  rw [i9421 hinj, i7154 hinj] at h
  linarith

theorem row4665 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11605 + (-1 : ℝ) * HLm Γ 5 L11701 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 4, 3] ![1, 0, 2, 4, 3] (by decide) L14163 L14162 (by decide)
  rw [i9422 hinj, i9423 hinj] at h
  linarith

theorem row4666 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11672 + (-1 : ℝ) * HLm Γ 5 L11635 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L14164 L11673 (by decide)
  rw [i7133 hinj, i9424 hinj] at h
  linarith

theorem row4667 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11669 + (-1 : ℝ) * HLm Γ 5 L11639 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L14166 L14165 (by decide)
  rw [i9425 hinj, i9426 hinj] at h
  linarith

theorem row4668 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11645 + (-1 : ℝ) * HLm Γ 5 L11680 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L11681 L11646 (by decide)
  rw [i7117 hinj, i7137 hinj] at h
  linarith

theorem row4669 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11647 + (-1 : ℝ) * HLm Γ 5 L11676 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L14168 L14167 (by decide)
  rw [i9427 hinj, i9428 hinj] at h
  linarith

theorem row4670 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11689 + (-1 : ℝ) * HLm Γ 5 L11656 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 4, 2] ![1, 0, 4, 2, 3] (by decide) L11657 L11690 (by decide)
  rw [i7144 hinj, i7123 hinj] at h
  linarith

theorem row4671 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11691 + (-1 : ℝ) * HLm Γ 5 L11660 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L11661 L11692 (by decide)
  rw [i7145 hinj, i7125 hinj] at h
  linarith

theorem row4672 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11662 + (-1 : ℝ) * HLm Γ 5 L9719 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 2, 4, 3] ![0, 1, 2, 4, 3] (by decide) L13789 L14169 (by decide)
  rw [i9429 hinj, i9060 hinj] at h
  linarith

theorem row4673 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11687 + (-1 : ℝ) * HLm Γ 5 L11664 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L11665 L11688 (by decide)
  rw [i7143 hinj, i7127 hinj] at h
  linarith

end EntropyBounds.TwoSet.Certs.R7A5
