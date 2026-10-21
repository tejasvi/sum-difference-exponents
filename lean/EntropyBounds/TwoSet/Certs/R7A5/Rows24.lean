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

theorem row3600 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L7241 + (-1 : ℝ) * HLm Γ 5 L6979 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 2, 4, 3] ![0, 1, 2, 4, 3] (by decide) L7225 L12642 (by decide)
  rw [i8002 hinj, i4284 hinj] at h
  linarith

theorem row3601 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12643 + (-1 : ℝ) * HLm Γ 5 L6979 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L7225 L12644 (by decide)
  rw [i8003 hinj, i4284 hinj] at h
  linarith

theorem row3602 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12643 + (-1 : ℝ) * HLm Γ 5 L2458 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L12646 L12645 (by decide)
  rw [i8004 hinj, i8005 hinj] at h
  linarith

theorem row3603 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2460 + (-1 : ℝ) * HLm Γ 5 L2708 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L12648 L12647 (by decide)
  rw [i8006 hinj, i8007 hinj] at h
  linarith

theorem row3604 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12649 + (-1 : ℝ) * HLm Γ 5 L2495 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 3, 2, 1, 4] ![0, 3, 2, 1, 4] (by decide) L2496 L12650 (by decide)
  rw [i8008 hinj, i1381 hinj] at h
  linarith

theorem row3605 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L1135 + (-1 : ℝ) * HLm Γ 5 L7416 = 0 := by
  have h := HLm_permB (Γ := Γ) ![3, 1, 2, 0, 4] ![3, 1, 2, 0, 4] (by decide) L7416 L12651 (by decide)
  rw [i8009 hinj] at h
  linarith

theorem row3606 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L1135 + (-1 : ℝ) * HLm Γ 5 L12649 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L12652 L12221 (by decide)
  rw [i7621 hinj, i8010 hinj] at h
  linarith

theorem row3607 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L1171 + (-1 : ℝ) * HLm Γ 5 L8130 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L12654 L12653 (by decide)
  rw [i8011 hinj, i8012 hinj] at h
  linarith

theorem row3608 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2462 + (-1 : ℝ) * HLm Γ 5 L2528 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L2529 L12655 (by decide)
  rw [i8013 hinj, i1402 hinj] at h
  linarith

theorem row3609 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2462 + (-1 : ℝ) * HLm Γ 5 L7197 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 4, 3] ![1, 0, 2, 4, 3] (by decide) L12656 L12655 (by decide)
  rw [i8013 hinj, i8014 hinj] at h
  linarith

theorem row3610 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2462 + (-1 : ℝ) * HLm Γ 5 L3087 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L3885 L12655 (by decide)
  rw [i8013 hinj, i2170 hinj] at h
  linarith

theorem row3611 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L1614 + (-1 : ℝ) * HLm Γ 5 L1771 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L12250 L12251 (by decide)
  rw [i7650 hinj, i7649 hinj] at h
  linarith

theorem row3612 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L1614 + (-1 : ℝ) * HLm Γ 5 L2505 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L12658 L12657 (by decide)
  rw [i8015 hinj, i8016 hinj] at h
  linarith

theorem row3613 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L1187 + (-1 : ℝ) * HLm Γ 5 L1686 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L12107 L12659 (by decide)
  rw [i8017 hinj, i7514 hinj] at h
  linarith

theorem row3614 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L745 + (-1 : ℝ) * HLm Γ 5 L2525 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L12661 L12660 (by decide)
  rw [i8018 hinj, i8019 hinj] at h
  linarith

theorem row3615 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12662 + (-1 : ℝ) * HLm Γ 5 L8656 = 0 := by
  have h := HLm_permB (Γ := Γ) ![3, 1, 2, 0, 4] ![3, 1, 2, 0, 4] (by decide) L8657 L12663 (by decide)
  rw [i8020 hinj, i5110 hinj] at h
  linarith

theorem row3616 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2480 + (-1 : ℝ) * HLm Γ 5 L7980 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 3, 2, 1, 4] ![0, 3, 2, 1, 4] (by decide) L12665 L12664 (by decide)
  rw [i8021 hinj, i8022 hinj] at h
  linarith

theorem row3617 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12662 + (-1 : ℝ) * HLm Γ 5 L2480 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L2481 L12666 (by decide)
  rw [i8023 hinj, i1369 hinj] at h
  linarith

theorem row3618 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2484 + (-1 : ℝ) * HLm Γ 5 L6836 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 3, 2, 1, 4] ![0, 3, 2, 1, 4] (by decide) L6837 L12667 (by decide)
  rw [i8024 hinj, i4071 hinj] at h
  linarith

theorem row3619 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L1323 + (-1 : ℝ) * HLm Γ 5 L6955 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L12669 L12668 (by decide)
  rw [i8025 hinj, i8026 hinj] at h
  linarith

theorem row3620 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L8396 + (-1 : ℝ) * HLm Γ 5 L2561 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L9799 L12670 (by decide)
  rw [i8027 hinj, i5825 hinj] at h
  linarith

theorem row3621 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2565 + (-1 : ℝ) * HLm Γ 5 L8398 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L12672 L12671 (by decide)
  rw [i8028 hinj, i8029 hinj] at h
  linarith

theorem row3622 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2565 + (-1 : ℝ) * HLm Γ 5 L1842 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L1843 L12673 (by decide)
  rw [i8030 hinj, i989 hinj] at h
  linarith

theorem row3623 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2565 + (-1 : ℝ) * HLm Γ 5 L1380 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L12291 L12674 (by decide)
  rw [i8031 hinj, i7687 hinj] at h
  linarith

theorem row3624 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L9947 + (-1 : ℝ) * HLm Γ 5 L12676 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 4, 2, 3, 1] ![0, 4, 2, 3, 1] (by decide) L12677 L12675 (by decide)
  rw [i8032 hinj, i8033 hinj] at h
  linarith

theorem row3625 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12678 + (-1 : ℝ) * HLm Γ 5 L8236 = 0 := by
  have h := HLm_permB (Γ := Γ) ![2, 1, 0, 3, 4] ![2, 1, 0, 3, 4] (by decide) L12680 L12679 (by decide)
  rw [i8034 hinj, i8035 hinj] at h
  linarith

theorem row3626 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L8574 + (-1 : ℝ) * HLm Γ 5 L12682 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 3, 2, 1, 4] ![0, 3, 2, 1, 4] (by decide) L12683 L12681 (by decide)
  rw [i8036 hinj, i8037 hinj] at h
  linarith

theorem row3627 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L9256 + (-1 : ℝ) * HLm Γ 5 L12682 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L12683 L12684 (by decide)
  rw [i8038 hinj, i8037 hinj] at h
  linarith

theorem row3628 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12676 + (-1 : ℝ) * HLm Γ 5 L2569 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 3, 2, 1, 4] ![0, 3, 2, 1, 4] (by decide) L12686 L12685 (by decide)
  rw [i8039 hinj, i8040 hinj] at h
  linarith

theorem row3629 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12678 + (-1 : ℝ) * HLm Γ 5 L2569 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L12686 L12687 (by decide)
  rw [i8041 hinj, i8040 hinj] at h
  linarith

theorem row3630 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2569 + (-1 : ℝ) * HLm Γ 5 L12682 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 4, 2] ![0, 1, 4, 2, 3] (by decide) L12683 L12688 (by decide)
  rw [i8042 hinj, i8037 hinj] at h
  linarith

theorem row3631 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L9908 + (-1 : ℝ) * HLm Γ 5 L847 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 4, 2] ![1, 0, 4, 2, 3] (by decide) L12096 L12689 (by decide)
  rw [i8043 hinj, i7503 hinj] at h
  linarith

theorem row3632 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2827 + (-1 : ℝ) * HLm Γ 5 L1428 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L12298 L12690 (by decide)
  rw [i8044 hinj, i7694 hinj] at h
  linarith

theorem row3633 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L656 + (-1 : ℝ) * HLm Γ 5 L2591 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L2592 L7831 (by decide)
  rw [i4623 hinj, i1447 hinj] at h
  linarith

theorem row3634 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2639 + (-1 : ℝ) * HLm Γ 5 L2808 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L2809 L2640 (by decide)
  rw [i1480 hinj, i1607 hinj] at h
  linarith

theorem row3635 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2805 + (-1 : ℝ) * HLm Γ 5 L2641 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L12692 L12691 (by decide)
  rw [i8045 hinj, i8046 hinj] at h
  linarith

theorem row3636 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L10564 + (-1 : ℝ) * HLm Γ 5 L1731 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 4, 2] ![0, 1, 4, 2, 3] (by decide) L6513 L12693 (by decide)
  rw [i8047 hinj, i3801 hinj] at h
  linarith

theorem row3637 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2670 + (-1 : ℝ) * HLm Γ 5 L2651 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L2652 L12694 (by decide)
  rw [i8048 hinj, i1488 hinj] at h
  linarith

theorem row3638 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L8466 + (-1 : ℝ) * HLm Γ 5 L2654 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L2655 L12695 (by decide)
  rw [i8049 hinj, i1490 hinj] at h
  linarith

theorem row3639 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L7321 + (-1 : ℝ) * HLm Γ 5 L2654 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L2655 L12696 (by decide)
  rw [i8050 hinj, i1490 hinj] at h
  linarith

theorem row3640 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2662 + (-1 : ℝ) * HLm Γ 5 L8504 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L12698 L12697 (by decide)
  rw [i8051 hinj, i8052 hinj] at h
  linarith

theorem row3641 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2662 + (-1 : ℝ) * HLm Γ 5 L9891 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 4, 3] ![1, 0, 2, 4, 3] (by decide) L9892 L12699 (by decide)
  rw [i8053 hinj, i5889 hinj] at h
  linarith

theorem row3642 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2664 + (-1 : ℝ) * HLm Γ 5 L904 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L12121 L12700 (by decide)
  rw [i8054 hinj, i7528 hinj] at h
  linarith

theorem row3643 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L1564 + (-1 : ℝ) * HLm Γ 5 L2664 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L12702 L12701 (by decide)
  rw [i8055 hinj, i8056 hinj] at h
  linarith

theorem row3644 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2683 + (-1 : ℝ) * HLm Γ 5 L2675 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L12704 L12703 (by decide)
  rw [i8057 hinj, i8058 hinj] at h
  linarith

theorem row3645 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2698 + (-1 : ℝ) * HLm Γ 5 L2817 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L2818 L12705 (by decide)
  rw [i8059 hinj, i1614 hinj] at h
  linarith

theorem row3646 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2698 + (-1 : ℝ) * HLm Γ 5 L8923 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L12707 L12706 (by decide)
  rw [i8060 hinj, i8061 hinj] at h
  linarith

theorem row3647 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2700 + (-1 : ℝ) * HLm Γ 5 L2813 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L10304 L12708 (by decide)
  rw [i8062 hinj, i6169 hinj] at h
  linarith

theorem row3648 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L7869 + (-1 : ℝ) * HLm Γ 5 L12709 = 0 := by
  have h := HLm_permB (Γ := Γ) ![4, 1, 2, 3, 0] ![4, 1, 2, 3, 0] (by decide) L12710 L7870 (by decide)
  rw [i4644 hinj, i8063 hinj] at h
  linarith

theorem row3649 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L9299 + (-1 : ℝ) * HLm Γ 5 L2726 = 0 := by
  have h := HLm_permB (Γ := Γ) ![4, 1, 2, 3, 0] ![4, 1, 2, 3, 0] (by decide) L2727 L12711 (by decide)
  rw [i8064 hinj, i1537 hinj] at h
  linarith

theorem row3650 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12709 + (-1 : ℝ) * HLm Γ 5 L2726 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L2727 L12710 (by decide)
  rw [i8063 hinj, i1537 hinj] at h
  linarith

theorem row3651 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2731 + (-1 : ℝ) * HLm Γ 5 L1264 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L12713 L12712 (by decide)
  rw [i8065 hinj, i8066 hinj] at h
  linarith

theorem row3652 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L8544 + (-1 : ℝ) * HLm Γ 5 L9344 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L12715 L12714 (by decide)
  rw [i8067 hinj, i8068 hinj] at h
  linarith

theorem row3653 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L9344 + (-1 : ℝ) * HLm Γ 5 L1710 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 4, 2] ![0, 1, 4, 2, 3] (by decide) L5703 L12715 (by decide)
  rw [i8068 hinj, i3239 hinj] at h
  linarith

theorem row3654 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L10069 + (-1 : ℝ) * HLm Γ 5 L1728 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L5708 L12716 (by decide)
  rw [i8069 hinj, i3243 hinj] at h
  linarith

theorem row3655 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11171 + (-1 : ℝ) * HLm Γ 5 L1728 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 4, 3, 2] ![0, 1, 4, 3, 2] (by decide) L5708 L12717 (by decide)
  rw [i8070 hinj, i3243 hinj] at h
  linarith

theorem row3656 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11126 + (-1 : ℝ) * HLm Γ 5 L2749 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 4, 3] ![1, 0, 2, 4, 3] (by decide) L12719 L12718 (by decide)
  rw [i8071 hinj, i8072 hinj] at h
  linarith

theorem row3657 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L5755 + (-1 : ℝ) * HLm Γ 5 L2749 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L12719 L12344 (by decide)
  rw [i7740 hinj, i8072 hinj] at h
  linarith

theorem row3658 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L1758 + (-1 : ℝ) * HLm Γ 5 L2749 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L12719 L12720 (by decide)
  rw [i8073 hinj, i8072 hinj] at h
  linarith

theorem row3659 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L1745 + (-1 : ℝ) * HLm Γ 5 L10502 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 4, 2] ![1, 0, 4, 2, 3] (by decide) L12721 L12346 (by decide)
  rw [i7742 hinj, i8074 hinj] at h
  linarith

theorem row3660 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L1967 + (-1 : ℝ) * HLm Γ 5 L2921 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 4, 2] ![0, 1, 4, 2, 3] (by decide) L2921 L1967 (by decide)
  linarith

theorem row3661 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L1968 + (-1 : ℝ) * HLm Γ 5 L11168 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 4, 2] ![1, 0, 4, 2, 3] (by decide) L11169 L1969 (by decide)
  rw [i1085 hinj, i6847 hinj] at h
  linarith

theorem row3662 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L1968 + (-1 : ℝ) * HLm Γ 5 L3036 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 4, 2] ![0, 1, 4, 2, 3] (by decide) L3037 L1969 (by decide)
  rw [i1085 hinj, i1726 hinj] at h
  linarith

theorem row3663 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3071 + (-1 : ℝ) * HLm Γ 5 L2851 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 2, 4, 3] ![0, 1, 2, 4, 3] (by decide) L2852 L3072 (by decide)
  rw [i1747 hinj, i1633 hinj] at h
  linarith

theorem row3664 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3122 + (-1 : ℝ) * HLm Γ 5 L2853 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 2, 4, 3] ![0, 1, 2, 4, 3] (by decide) L2854 L12374 (by decide)
  rw [i7767 hinj, i1634 hinj] at h
  linarith

theorem row3665 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3273 + (-1 : ℝ) * HLm Γ 5 L2888 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 4, 2, 3, 1] ![0, 4, 2, 3, 1] (by decide) L2888 L12722 (by decide)
  rw [i8075 hinj] at h
  linarith

theorem row3666 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3616 + (-1 : ℝ) * HLm Γ 5 L12724 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 4, 2, 3, 1] ![0, 4, 2, 3, 1] (by decide) L12725 L12723 (by decide)
  rw [i8076 hinj, i8077 hinj] at h
  linarith

theorem row3667 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L4777 + (-1 : ℝ) * HLm Γ 5 L12724 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L12725 L12726 (by decide)
  rw [i8078 hinj, i8077 hinj] at h
  linarith

theorem row3668 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12724 + (-1 : ℝ) * HLm Γ 5 L2891 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L12727 L12725 (by decide)
  rw [i8077 hinj, i8079 hinj] at h
  linarith

theorem row3669 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L4061 + (-1 : ℝ) * HLm Γ 5 L12728 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 4, 2, 3, 1] ![0, 4, 2, 3, 1] (by decide) L12728 L4061 (by decide)
  linarith

theorem row3670 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12728 + (-1 : ℝ) * HLm Γ 5 L2910 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L2910 L12728 (by decide)
  linarith

theorem row3671 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3671 + (-1 : ℝ) * HLm Γ 5 L2911 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L3634 L3672 (by decide)
  rw [i2055 hinj, i2036 hinj] at h
  linarith

theorem row3672 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2915 + (-1 : ℝ) * HLm Γ 5 L3277 = 0 := by
  have h := HLm_permB (Γ := Γ) ![4, 1, 2, 3, 0] ![4, 1, 2, 3, 0] (by decide) L11188 L2916 (by decide)
  rw [i1663 hinj, i6859 hinj] at h
  linarith

theorem row3673 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3388 + (-1 : ℝ) * HLm Γ 5 L7133 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 4, 2, 3, 1] ![0, 4, 2, 3, 1] (by decide) L12729 L3389 (by decide)
  rw [i1903 hinj, i8080 hinj] at h
  linarith

theorem row3674 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L7133 + (-1 : ℝ) * HLm Γ 5 L2919 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L2919 L12729 (by decide)
  rw [i8080 hinj] at h
  linarith

theorem row3675 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3673 + (-1 : ℝ) * HLm Γ 5 L2923 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 4, 2] ![0, 1, 4, 2, 3] (by decide) L12730 L3673 (by decide)
  rw [i8081 hinj] at h
  linarith

theorem row3676 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2925 + (-1 : ℝ) * HLm (mirror Γ) 5 L2974 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 4, 1, 2, 3] ![0, 2, 3, 4, 1] (by decide) L2975 L12731 (by decide)
  rw [i1696 hinj', i8082 hinj] at h
  linarith

theorem row3677 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3825 + (-1 : ℝ) * HLm Γ 5 L12733 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 4, 2, 3, 1] ![0, 4, 2, 3, 1] (by decide) L12734 L12732 (by decide)
  rw [i8083 hinj, i8084 hinj] at h
  linarith

theorem row3678 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12733 + (-1 : ℝ) * HLm Γ 5 L2927 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 4, 3] ![1, 0, 2, 4, 3] (by decide) L12736 L12735 (by decide)
  rw [i8085 hinj, i8086 hinj] at h
  linarith

theorem row3679 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3729 + (-1 : ℝ) * HLm Γ 5 L12738 = 0 := by
  have h := HLm_permB (Γ := Γ) ![4, 1, 2, 3, 0] ![4, 1, 2, 3, 0] (by decide) L12739 L12737 (by decide)
  rw [i8087 hinj, i8088 hinj] at h
  linarith

theorem row3680 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12738 + (-1 : ℝ) * HLm Γ 5 L2935 = 0 := by
  have h := HLm_permB (Γ := Γ) ![2, 1, 0, 3, 4] ![2, 1, 0, 3, 4] (by decide) L2936 L12740 (by decide)
  rw [i8089 hinj, i1673 hinj] at h
  linarith

theorem row3681 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3783 + (-1 : ℝ) * HLm Γ 5 L2955 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 4, 2] ![0, 1, 4, 2, 3] (by decide) L12742 L12741 (by decide)
  rw [i8090 hinj, i8091 hinj] at h
  linarith

theorem row3682 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2963 + (-1 : ℝ) * HLm Γ 5 L4225 = 0 := by
  have h := HLm_permB (Γ := Γ) ![3, 1, 2, 0, 4] ![3, 1, 2, 0, 4] (by decide) L4225 L12743 (by decide)
  rw [i8092 hinj] at h
  linarith

theorem row3683 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2963 + (-1 : ℝ) * HLm Γ 5 L3336 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L3336 L2964 (by decide)
  rw [i1688 hinj] at h
  linarith

theorem row3684 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L4018 + (-1 : ℝ) * HLm Γ 5 L2987 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 2, 4, 3] ![0, 1, 2, 4, 3] (by decide) L12745 L12744 (by decide)
  rw [i8093 hinj, i8094 hinj] at h
  linarith

theorem row3685 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L4110 + (-1 : ℝ) * HLm Γ 5 L2990 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 2, 4, 3] ![0, 1, 2, 4, 3] (by decide) L12746 L4111 (by decide)
  rw [i2293 hinj, i8095 hinj] at h
  linarith

theorem row3686 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L4050 + (-1 : ℝ) * HLm Γ 5 L3003 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 2, 4, 3] ![0, 1, 2, 4, 3] (by decide) L3004 L4051 (by decide)
  rw [i2260 hinj, i1711 hinj] at h
  linarith

theorem row3687 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L4554 + (-1 : ℝ) * HLm Γ 5 L3012 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 4, 2] ![0, 1, 4, 2, 3] (by decide) L12748 L12747 (by decide)
  rw [i8096 hinj, i8097 hinj] at h
  linarith

theorem row3688 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L4083 + (-1 : ℝ) * HLm Γ 5 L3019 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 2, 4, 3] ![0, 1, 2, 4, 3] (by decide) L3020 L4084 (by decide)
  rw [i2278 hinj, i1718 hinj] at h
  linarith

theorem row3689 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3032 + (-1 : ℝ) * HLm Γ 5 L11546 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L11547 L3033 (by decide)
  rw [i1724 hinj, i7058 hinj] at h
  linarith

theorem row3690 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3788 + (-1 : ℝ) * HLm Γ 5 L3038 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 4, 2] ![0, 1, 4, 2, 3] (by decide) L3039 L12749 (by decide)
  rw [i8098 hinj, i1727 hinj] at h
  linarith

theorem row3691 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3045 + (-1 : ℝ) * HLm Γ 5 L3567 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L3568 L12750 (by decide)
  rw [i8099 hinj, i2000 hinj] at h
  linarith

theorem row3692 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11711 + (-1 : ℝ) * HLm Γ 5 L12751 = 0 := by
  have h := HLm_permB (Γ := Γ) ![3, 1, 2, 0, 4] ![3, 1, 2, 0, 4] (by decide) L12752 L11712 (by decide)
  rw [i7158 hinj, i8100 hinj] at h
  linarith

theorem row3693 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3865 + (-1 : ℝ) * HLm Γ 5 L3050 = 0 := by
  have h := HLm_permB (Γ := Γ) ![2, 1, 0, 3, 4] ![2, 1, 0, 3, 4] (by decide) L3051 L3866 (by decide)
  rw [i2159 hinj, i1735 hinj] at h
  linarith

theorem row3694 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12751 + (-1 : ℝ) * HLm Γ 5 L3050 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L3051 L12752 (by decide)
  rw [i8100 hinj, i1735 hinj] at h
  linarith

theorem row3695 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11707 + (-1 : ℝ) * HLm Γ 5 L12754 = 0 := by
  have h := HLm_permB (Γ := Γ) ![3, 1, 2, 0, 4] ![3, 1, 2, 0, 4] (by decide) L12755 L12753 (by decide)
  rw [i8101 hinj, i8102 hinj] at h
  linarith

theorem row3696 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L4142 + (-1 : ℝ) * HLm Γ 5 L3052 = 0 := by
  have h := HLm_permB (Γ := Γ) ![2, 1, 0, 3, 4] ![2, 1, 0, 3, 4] (by decide) L12757 L12756 (by decide)
  rw [i8103 hinj, i8104 hinj] at h
  linarith

theorem row3697 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12754 + (-1 : ℝ) * HLm Γ 5 L3052 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 4, 2] ![0, 1, 4, 2, 3] (by decide) L12757 L12755 (by decide)
  rw [i8102 hinj, i8104 hinj] at h
  linarith

theorem row3698 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3974 + (-1 : ℝ) * HLm Γ 5 L3058 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 3, 2, 1, 4] ![0, 3, 2, 1, 4] (by decide) L12758 L3975 (by decide)
  rw [i2218 hinj, i8105 hinj] at h
  linarith

theorem row3699 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12759 + (-1 : ℝ) * HLm Γ 5 L4177 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 4, 2] ![0, 1, 4, 2, 3] (by decide) L12761 L12760 (by decide)
  rw [i8106 hinj, i8107 hinj] at h
  linarith

theorem row3700 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12759 + (-1 : ℝ) * HLm Γ 5 L3078 = 0 := by
  have h := HLm_permB (Γ := Γ) ![4, 1, 2, 3, 0] ![4, 1, 2, 3, 0] (by decide) L12763 L12762 (by decide)
  rw [i8108 hinj, i8109 hinj] at h
  linarith

theorem row3701 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3081 + (-1 : ℝ) * HLm Γ 5 L4045 = 0 := by
  have h := HLm_permB (Γ := Γ) ![3, 1, 2, 0, 4] ![3, 1, 2, 0, 4] (by decide) L12765 L12764 (by decide)
  rw [i8110 hinj, i8111 hinj] at h
  linarith

theorem row3702 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3086 + (-1 : ℝ) * HLm (mirror Γ) 5 L3377 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L3378 L12766 (by decide)
  rw [i1897 hinj', i8112 hinj] at h
  linarith

theorem row3703 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3096 + (-1 : ℝ) * HLm Γ 5 L2102 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 4, 3] ![1, 0, 2, 4, 3] (by decide) L3964 L3096 (by decide)
  rw [i2212 hinj] at h
  linarith

theorem row3704 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3101 + (-1 : ℝ) * HLm Γ 5 L3096 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L3096 L12767 (by decide)
  rw [i8113 hinj] at h
  linarith

theorem row3705 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3096 + (-1 : ℝ) * HLm Γ 5 L3100 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 2, 4, 3] ![0, 1, 2, 4, 3] (by decide) L3100 L3096 (by decide)
  linarith

theorem row3706 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3958 + (-1 : ℝ) * HLm Γ 5 L3098 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 4, 3] ![1, 0, 2, 4, 3] (by decide) L12768 L3959 (by decide)
  rw [i2209 hinj, i8114 hinj] at h
  linarith

theorem row3707 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11575 + (-1 : ℝ) * HLm Γ 5 L3114 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 2, 4, 3] ![0, 1, 2, 4, 3] (by decide) L12769 L11576 (by decide)
  rw [i7074 hinj, i8115 hinj] at h
  linarith

theorem row3708 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L4117 + (-1 : ℝ) * HLm Γ 5 L3118 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 2, 4, 3] ![0, 1, 2, 4, 3] (by decide) L4116 L12770 (by decide)
  rw [i8116 hinj, i2296 hinj] at h
  linarith

theorem row3709 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3489 + (-1 : ℝ) * HLm Γ 5 L3125 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 2, 4, 3] ![0, 1, 2, 4, 3] (by decide) L12772 L12771 (by decide)
  rw [i8117 hinj, i8118 hinj] at h
  linarith

theorem row3710 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3126 + (-1 : ℝ) * HLm Γ 5 L4022 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 2, 4, 3] ![0, 1, 2, 4, 3] (by decide) L4023 L12773 (by decide)
  rw [i8119 hinj, i2245 hinj] at h
  linarith

theorem row3711 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3258 + (-1 : ℝ) * HLm Γ 5 L2210 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 2, 4, 3] ![0, 1, 2, 4, 3] (by decide) L4260 L12774 (by decide)
  rw [i8120 hinj, i2384 hinj] at h
  linarith

theorem row3712 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L4168 + (-1 : ℝ) * HLm Γ 5 L3140 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 4, 2, 3, 1] ![0, 4, 2, 3, 1] (by decide) L8074 L4169 (by decide)
  rw [i2328 hinj, i4760 hinj] at h
  linarith

theorem row3713 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3747 + (-1 : ℝ) * HLm Γ 5 L3171 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L12776 L12775 (by decide)
  rw [i8121 hinj, i8122 hinj] at h
  linarith

theorem row3714 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12777 + (-1 : ℝ) * HLm Γ 5 L5018 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 4, 2, 3, 1] ![0, 4, 2, 3, 1] (by decide) L5019 L12778 (by decide)
  rw [i8123 hinj, i2827 hinj] at h
  linarith

theorem row3715 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12779 + (-1 : ℝ) * HLm Γ 5 L3282 = 0 := by
  have h := HLm_permB (Γ := Γ) ![4, 1, 2, 3, 0] ![4, 1, 2, 3, 0] (by decide) L12781 L12780 (by decide)
  rw [i8124 hinj, i8125 hinj] at h
  linarith

theorem row3716 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3189 + (-1 : ℝ) * HLm Γ 5 L12777 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 4, 3] ![1, 0, 2, 4, 3] (by decide) L12783 L12782 (by decide)
  rw [i8126 hinj, i8127 hinj] at h
  linarith

theorem row3717 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3189 + (-1 : ℝ) * HLm Γ 5 L12779 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 4, 2] ![0, 1, 4, 2, 3] (by decide) L12785 L12784 (by decide)
  rw [i8128 hinj, i8129 hinj] at h
  linarith

theorem row3718 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L4095 + (-1 : ℝ) * HLm Γ 5 L3194 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 4, 2] ![0, 1, 4, 2, 3] (by decide) L12787 L12786 (by decide)
  rw [i8130 hinj, i8131 hinj] at h
  linarith

theorem row3719 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L4638 + (-1 : ℝ) * HLm Γ 5 L2310 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 3, 2, 1, 4] ![0, 3, 2, 1, 4] (by decide) L12559 L12788 (by decide)
  rw [i8132 hinj, i7926 hinj] at h
  linarith

theorem row3720 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2310 + (-1 : ℝ) * HLm Γ 5 L3222 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L12789 L12559 (by decide)
  rw [i7926 hinj, i8133 hinj] at h
  linarith

theorem row3721 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L4345 + (-1 : ℝ) * HLm Γ 5 L3241 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L3242 L12790 (by decide)
  rw [i8134 hinj, i1830 hinj] at h
  linarith

theorem row3722 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3250 + (-1 : ℝ) * HLm Γ 5 L3241 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 2, 4, 3] ![0, 1, 2, 4, 3] (by decide) L3242 L12791 (by decide)
  rw [i8135 hinj, i1830 hinj] at h
  linarith

theorem row3723 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L5306 + (-1 : ℝ) * HLm Γ 5 L3243 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L12793 L12792 (by decide)
  rw [i8136 hinj, i8137 hinj] at h
  linarith

theorem row3724 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12794 + (-1 : ℝ) * HLm Γ 5 L5234 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 4, 2] ![0, 1, 4, 2, 3] (by decide) L5235 L12795 (by decide)
  rw [i8138 hinj, i2949 hinj] at h
  linarith

theorem row3725 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3475 + (-1 : ℝ) * HLm Γ 5 L12797 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 2, 4, 3] ![0, 1, 2, 4, 3] (by decide) L12798 L12796 (by decide)
  rw [i8139 hinj, i8140 hinj] at h
  linarith

theorem row3726 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12794 + (-1 : ℝ) * HLm Γ 5 L3252 = 0 := by
  have h := HLm_permB (Γ := Γ) ![4, 1, 2, 3, 0] ![4, 1, 2, 3, 0] (by decide) L12800 L12799 (by decide)
  rw [i8141 hinj, i8142 hinj] at h
  linarith

theorem row3727 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12797 + (-1 : ℝ) * HLm Γ 5 L3252 = 0 := by
  have h := HLm_permB (Γ := Γ) ![3, 1, 2, 0, 4] ![3, 1, 2, 0, 4] (by decide) L12800 L12801 (by decide)
  rw [i8143 hinj, i8142 hinj] at h
  linarith

theorem row3728 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3263 + (-1 : ℝ) * HLm Γ 5 L4291 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 2, 4, 3] ![0, 1, 2, 4, 3] (by decide) L4292 L12802 (by decide)
  rw [i8144 hinj, i2402 hinj] at h
  linarith

theorem row3729 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3299 + (-1 : ℝ) * HLm Γ 5 L12804 = 0 := by
  have h := HLm_permB (Γ := Γ) ![4, 1, 2, 3, 0] ![4, 1, 2, 3, 0] (by decide) L12805 L12803 (by decide)
  rw [i8145 hinj, i8146 hinj] at h
  linarith

theorem row3730 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12804 + (-1 : ℝ) * HLm Γ 5 L3271 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L12807 L12806 (by decide)
  rw [i8147 hinj, i8148 hinj] at h
  linarith

theorem row3731 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12808 + (-1 : ℝ) * HLm Γ 5 L4364 = 0 := by
  have h := HLm_permB (Γ := Γ) ![4, 1, 2, 3, 0] ![4, 1, 2, 3, 0] (by decide) L5383 L12809 (by decide)
  rw [i8149 hinj, i3037 hinj] at h
  linarith

theorem row3732 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12808 + (-1 : ℝ) * HLm Γ 5 L3274 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L12811 L12810 (by decide)
  rw [i8150 hinj, i8151 hinj] at h
  linarith

theorem row3733 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L4499 + (-1 : ℝ) * HLm Γ 5 L3284 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L12813 L12812 (by decide)
  rw [i8152 hinj, i8153 hinj] at h
  linarith

theorem row3734 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L4348 + (-1 : ℝ) * HLm Γ 5 L3296 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 2, 4, 3] ![0, 1, 2, 4, 3] (by decide) L12815 L12814 (by decide)
  rw [i8154 hinj, i8155 hinj] at h
  linarith

theorem row3735 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3307 + (-1 : ℝ) * HLm Γ 5 L4311 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 4, 2] ![0, 1, 4, 2, 3] (by decide) L12817 L12816 (by decide)
  rw [i8156 hinj, i8157 hinj] at h
  linarith

theorem row3736 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3309 + (-1 : ℝ) * HLm Γ 5 L4322 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 4, 2] ![0, 1, 4, 2, 3] (by decide) L12819 L12818 (by decide)
  rw [i8158 hinj, i8159 hinj] at h
  linarith

theorem row3737 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3316 + (-1 : ℝ) * HLm Γ 5 L3519 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L12821 L12820 (by decide)
  rw [i8160 hinj, i8161 hinj] at h
  linarith

theorem row3738 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3321 + (-1 : ℝ) * HLm (mirror Γ) 5 L3558 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![1, 4, 0, 2, 3] ![2, 0, 3, 4, 1] (by decide) L12823 L12822 (by decide)
  rw [i8163 hinj', i8162 hinj] at h
  linarith

theorem row3739 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3321 + (-1 : ℝ) * HLm (mirror Γ) 5 L7257 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![4, 1, 0, 2, 3] ![2, 1, 3, 4, 0] (by decide) L7257 L12822 (by decide)
  rw [i8162 hinj] at h
  linarith

theorem row3740 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3321 + (-1 : ℝ) * HLm (mirror Γ) 5 L7259 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![4, 1, 2, 0, 3] ![3, 1, 2, 4, 0] (by decide) L7259 L12822 (by decide)
  rw [i8162 hinj] at h
  linarith

theorem row3741 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3558 + (-1 : ℝ) * HLm Γ 5 L3321 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 4, 2] ![1, 0, 4, 2, 3] (by decide) L3321 L12823 (by decide)
  rw [i8163 hinj] at h
  linarith

theorem row3742 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L4423 + (-1 : ℝ) * HLm Γ 5 L3324 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 4, 2] ![0, 1, 4, 2, 3] (by decide) L12824 L4423 (by decide)
  rw [i8164 hinj] at h
  linarith

theorem row3743 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L4446 + (-1 : ℝ) * HLm Γ 5 L3329 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 4, 2] ![0, 1, 4, 2, 3] (by decide) L12826 L12825 (by decide)
  rw [i8165 hinj, i8166 hinj] at h
  linarith

theorem row3744 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L4936 + (-1 : ℝ) * HLm Γ 5 L3333 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L12828 L12827 (by decide)
  rw [i8167 hinj, i8168 hinj] at h
  linarith

theorem row3745 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L4186 + (-1 : ℝ) * HLm Γ 5 L12830 = 0 := by
  have h := HLm_permB (Γ := Γ) ![3, 1, 2, 0, 4] ![3, 1, 2, 0, 4] (by decide) L12831 L12829 (by decide)
  rw [i8169 hinj, i8170 hinj] at h
  linarith

theorem row3746 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L4602 + (-1 : ℝ) * HLm Γ 5 L12833 = 0 := by
  have h := HLm_permB (Γ := Γ) ![4, 1, 2, 3, 0] ![4, 1, 2, 3, 0] (by decide) L12834 L12832 (by decide)
  rw [i8171 hinj, i8172 hinj] at h
  linarith

theorem row3747 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L4513 + (-1 : ℝ) * HLm Γ 5 L12836 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 3, 2, 1, 4] ![0, 3, 2, 1, 4] (by decide) L12837 L12835 (by decide)
  rw [i8173 hinj, i8174 hinj] at h
  linarith

theorem row3748 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12830 + (-1 : ℝ) * HLm Γ 5 L3340 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 4, 3] ![1, 0, 2, 4, 3] (by decide) L3341 L12831 (by decide)
  rw [i8170 hinj, i1880 hinj] at h
  linarith

theorem row3749 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12833 + (-1 : ℝ) * HLm Γ 5 L3340 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L3341 L12834 (by decide)
  rw [i8172 hinj, i1880 hinj] at h
  linarith

end EntropyBounds.TwoSet.Certs.R7A5
