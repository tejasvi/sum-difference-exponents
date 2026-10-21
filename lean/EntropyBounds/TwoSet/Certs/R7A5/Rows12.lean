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

theorem row1800 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7306 + (1 : ℝ) * HLm Γ 5 L8621 + (-1 : ℝ) * HLm Γ 5 L1564 + (-1 : ℝ) * HLm Γ 5 L7304 := by
  have h := HLm_submod hΓ [F0] L7305 [F2]
  rw [show [F0] ++ L7305 ++ [F2] = L8623 from rfl, show [F0] ++ L7305 = L7307 from rfl,
    show L7305 ++ [F2] = L8622 from rfl] at h
  rw [i5092 hinj, i4331 hinj, i5091 hinj, i4330 hinj] at h
  linarith

theorem row1801 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8066 + (1 : ℝ) * HLm Γ 5 L8625 + (-1 : ℝ) * HLm Γ 5 L8627 + (-1 : ℝ) * HLm Γ 5 L7304 := by
  have h := HLm_submod hΓ [F210] L7305 [F55]
  rw [show [F210] ++ L7305 ++ [F55] = L8628 from rfl, show [F210] ++ L7305 = L8624 from rfl,
    show L7305 ++ [F55] = L8626 from rfl] at h
  rw [i5095 hinj, i5093 hinj, i5094 hinj, i4330 hinj] at h
  linarith

theorem row1802 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3396 + (1 : ℝ) * HLm Γ 5 L8629 + (-1 : ℝ) * HLm Γ 5 L8631 + (-1 : ℝ) * HLm Γ 5 L3394 := by
  have h := HLm_submod hΓ [F0] L3395 [F34]
  rw [show [F0] ++ L3395 ++ [F34] = L8632 from rfl, show [F0] ++ L3395 = L3397 from rfl,
    show L3395 ++ [F34] = L8630 from rfl] at h
  rw [i5097 hinj, i1907 hinj, i5096 hinj, i1906 hinj] at h
  linarith

theorem row1803 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6884 + (1 : ℝ) * HLm Γ 5 L8634 + (-1 : ℝ) * HLm Γ 5 L8636 + (-1 : ℝ) * HLm Γ 5 L2873 := by
  have h := HLm_submod hΓ [F0] L4185 [F34]
  rw [show [F0] ++ L4185 ++ [F34] = L8637 from rfl, show [F0] ++ L4185 = L8633 from rfl,
    show L4185 ++ [F34] = L8635 from rfl] at h
  rw [i5100 hinj, i5098 hinj, i5099 hinj, i2337 hinj] at h
  linarith

theorem row1804 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3415 + (1 : ℝ) * HLm Γ 5 L8638 + (-1 : ℝ) * HLm Γ 5 L8640 + (-1 : ℝ) * HLm Γ 5 L3413 := by
  have h := HLm_submod hΓ [F16] L3414 [F67]
  rw [show [F16] ++ L3414 ++ [F67] = L8641 from rfl, show [F16] ++ L3414 = L3416 from rfl,
    show L3414 ++ [F67] = L8639 from rfl] at h
  rw [i5102 hinj, i1917 hinj, i5101 hinj, i1916 hinj] at h
  linarith

theorem row1805 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8642 + (1 : ℝ) * HLm Γ 5 L8644 + (-1 : ℝ) * HLm Γ 5 L8646 + (-1 : ℝ) * HLm Γ 5 L8648 := by
  have h := HLm_submod hΓ [F210] L8649 [F17]
  rw [show [F210] ++ L8649 ++ [F17] = L8647 from rfl, show [F210] ++ L8649 = L8643 from rfl,
    show L8649 ++ [F17] = L8645 from rfl] at h
  rw [i5105 hinj, i5103 hinj, i5104 hinj, i5106 hinj] at h
  linarith

theorem row1806 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8650 + (1 : ℝ) * HLm Γ 5 L8652 + (-1 : ℝ) * HLm Γ 5 L8654 + (-1 : ℝ) * HLm Γ 5 L8656 := by
  have h := HLm_submod hΓ [F210] L8657 [F43]
  rw [show [F210] ++ L8657 ++ [F43] = L8655 from rfl, show [F210] ++ L8657 = L8651 from rfl,
    show L8657 ++ [F43] = L8653 from rfl] at h
  rw [i5109 hinj, i5107 hinj, i5108 hinj, i5110 hinj] at h
  linarith

theorem row1807 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8658 + (1 : ℝ) * HLm Γ 5 L8660 + (-1 : ℝ) * HLm Γ 5 L8662 + (-1 : ℝ) * HLm Γ 5 L8664 := by
  have h := HLm_submod hΓ [F67] L8665 [F27]
  rw [show [F67] ++ L8665 ++ [F27] = L8663 from rfl, show [F67] ++ L8665 = L8659 from rfl,
    show L8665 ++ [F27] = L8661 from rfl] at h
  rw [i5113 hinj, i5111 hinj, i5112 hinj, i5114 hinj] at h
  linarith

theorem row1808 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8666 + (1 : ℝ) * HLm Γ 5 L8668 + (-1 : ℝ) * HLm Γ 5 L8670 + (-1 : ℝ) * HLm Γ 5 L8672 := by
  have h := HLm_submod hΓ [F210] L8673 [F43]
  rw [show [F210] ++ L8673 ++ [F43] = L8671 from rfl, show [F210] ++ L8673 = L8667 from rfl,
    show L8673 ++ [F43] = L8669 from rfl] at h
  rw [i5117 hinj, i5115 hinj, i5116 hinj, i5118 hinj] at h
  linarith

theorem row1809 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8674 + (1 : ℝ) * HLm Γ 5 L8676 + (-1 : ℝ) * HLm Γ 5 L8678 + (-1 : ℝ) * HLm Γ 5 L3427 := by
  have h := HLm_submod hΓ [F210] L7349 [F17]
  rw [show [F210] ++ L7349 ++ [F17] = L8679 from rfl, show [F210] ++ L7349 = L8675 from rfl,
    show L7349 ++ [F17] = L8677 from rfl] at h
  rw [i5121 hinj, i5119 hinj, i5120 hinj, i4355 hinj] at h
  linarith

theorem row1810 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8680 + (1 : ℝ) * HLm Γ 5 L4628 + (-1 : ℝ) * HLm Γ 5 L4630 + (-1 : ℝ) * HLm Γ 5 L8682 := by
  have h := HLm_submod hΓ [F1] L8683 [F217]
  rw [show [F1] ++ L8683 ++ [F217] = L5909 from rfl, show [F1] ++ L8683 = L8681 from rfl,
    show L8683 ++ [F217] = L5914 from rfl] at h
  rw [i3374 hinj, i5122 hinj, i3377 hinj, i5123 hinj] at h
  linarith

theorem row1811 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8684 + (1 : ℝ) * HLm Γ 5 L7810 + (-1 : ℝ) * HLm Γ 5 L8686 + (-1 : ℝ) * HLm Γ 5 L7807 := by
  have h := HLm_submod hΓ [F107] L7808 [F210]
  rw [show [F107] ++ L7808 ++ [F210] = L8687 from rfl, show [F107] ++ L7808 = L8685 from rfl,
    show L7808 ++ [F210] = L7811 from rfl] at h
  rw [i5125 hinj, i5124 hinj, i4613 hinj, i4612 hinj] at h
  linarith

theorem row1812 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7232 + (1 : ℝ) * HLm Γ 5 L8689 + (-1 : ℝ) * HLm Γ 5 L8691 + (-1 : ℝ) * HLm Γ 5 L7354 := by
  have h := HLm_submod hΓ [F1] L7355 [F85]
  rw [show [F1] ++ L7355 ++ [F85] = L8692 from rfl, show [F1] ++ L7355 = L8688 from rfl,
    show L7355 ++ [F85] = L8690 from rfl] at h
  rw [i5128 hinj, i5126 hinj, i5127 hinj, i4358 hinj] at h
  linarith

theorem row1813 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7604 + (1 : ℝ) * HLm Γ 5 L8694 + (-1 : ℝ) * HLm Γ 5 L8696 + (-1 : ℝ) * HLm Γ 5 L3167 := by
  have h := HLm_submod hΓ [F1] L4040 [F7]
  rw [show [F1] ++ L4040 ++ [F7] = L8697 from rfl, show [F1] ++ L4040 = L8693 from rfl,
    show L4040 ++ [F7] = L8695 from rfl] at h
  rw [i5131 hinj, i5129 hinj, i5130 hinj, i2254 hinj] at h
  linarith

theorem row1814 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7369 + (1 : ℝ) * HLm Γ 5 L8698 + (-1 : ℝ) * HLm Γ 5 L8700 + (-1 : ℝ) * HLm Γ 5 L6960 := by
  have h := HLm_submod hΓ [F51] L6961 [F16]
  rw [show [F51] ++ L6961 ++ [F16] = L8701 from rfl, show [F51] ++ L6961 = L7370 from rfl,
    show L6961 ++ [F16] = L8699 from rfl] at h
  rw [i5133 hinj, i4367 hinj, i5132 hinj, i4135 hinj] at h
  linarith

theorem row1815 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8702 + (1 : ℝ) * HLm Γ 5 L7375 + (-1 : ℝ) * HLm Γ 5 L8705 + (-1 : ℝ) * HLm Γ 5 L7373 := by
  have h := HLm_submod hΓ [F21] L8707 [F210]
  rw [show [F21] ++ L8707 ++ [F210] = L8706 from rfl, show [F21] ++ L8707 = L8703 from rfl,
    show L8707 ++ [F210] = L8704 from rfl] at h
  rw [i5136 hinj, i5134 hinj, i5135 hinj, i5137 hinj] at h
  linarith

theorem row1816 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L950 + (1 : ℝ) * HLm Γ 5 L3436 + (-1 : ℝ) * HLm Γ 5 L8710 + (-1 : ℝ) * HLm Γ 5 L3434 := by
  have h := HLm_submod hΓ [F9] L3435 [F236]
  rw [show [F9] ++ L3435 ++ [F236] = L8711 from rfl, show [F9] ++ L3435 = L8708 from rfl,
    show L3435 ++ [F236] = L8709 from rfl] at h
  rw [i5140 hinj, i5138 hinj, i5139 hinj, i1927 hinj] at h
  linarith

theorem row1817 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8712 + (1 : ℝ) * HLm Γ 5 L7383 + (-1 : ℝ) * HLm Γ 5 L8715 + (-1 : ℝ) * HLm Γ 5 L4642 := by
  have h := HLm_submod hΓ [F21] L4643 [F210]
  rw [show [F21] ++ L4643 ++ [F210] = L8716 from rfl, show [F21] ++ L4643 = L8713 from rfl,
    show L4643 ++ [F210] = L8714 from rfl] at h
  rw [i5143 hinj, i5141 hinj, i5142 hinj, i2608 hinj] at h
  linarith

theorem row1818 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8717 + (1 : ℝ) * HLm Γ 5 L8719 + (-1 : ℝ) * HLm Γ 5 L8721 + (-1 : ℝ) * HLm Γ 5 L8723 := by
  have h := HLm_submod hΓ [F17] L8724 [F219]
  rw [show [F17] ++ L8724 ++ [F219] = L8722 from rfl, show [F17] ++ L8724 = L8718 from rfl,
    show L8724 ++ [F219] = L8720 from rfl] at h
  rw [i5146 hinj, i5144 hinj, i5145 hinj, i5147 hinj] at h
  linarith

theorem row1819 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8725 + (1 : ℝ) * HLm Γ 5 L8727 + (-1 : ℝ) * HLm Γ 5 L8729 + (-1 : ℝ) * HLm Γ 5 L7389 := by
  have h := HLm_submod hΓ [F236] L8731 [F45]
  rw [show [F236] ++ L8731 ++ [F45] = L8730 from rfl, show [F236] ++ L8731 = L8726 from rfl,
    show L8731 ++ [F45] = L8728 from rfl] at h
  rw [i5150 hinj, i5148 hinj, i5149 hinj, i5151 hinj] at h
  linarith

theorem row1820 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7656 + (1 : ℝ) * HLm Γ 5 L7391 + (-1 : ℝ) * HLm Γ 5 L8734 + (-1 : ℝ) * HLm Γ 5 L6822 := by
  have h := HLm_submod hΓ [F16] L6822 [F17]
  rw [show [F16] ++ L6822 ++ [F17] = L8735 from rfl, show [F16] ++ L6822 = L8732 from rfl,
    show L6822 ++ [F17] = L8733 from rfl] at h
  rw [i5154 hinj, i5152 hinj, i5153 hinj] at h
  linarith

theorem row1821 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7992 + (1 : ℝ) * HLm Γ 5 L8737 + (-1 : ℝ) * HLm Γ 5 L8739 + (-1 : ℝ) * HLm Γ 5 L8741 := by
  have h := HLm_submod hΓ [F67] L8742 [F210]
  rw [show [F67] ++ L8742 ++ [F210] = L8740 from rfl, show [F67] ++ L8742 = L8736 from rfl,
    show L8742 ++ [F210] = L8738 from rfl] at h
  rw [i5157 hinj, i5155 hinj, i5156 hinj, i5158 hinj] at h
  linarith

theorem row1822 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8743 + (1 : ℝ) * HLm Γ 5 L8745 + (-1 : ℝ) * HLm Γ 5 L8747 + (-1 : ℝ) * HLm Γ 5 L8749 := by
  have h := HLm_submod hΓ [F44] L8750 [F219]
  rw [show [F44] ++ L8750 ++ [F219] = L8748 from rfl, show [F44] ++ L8750 = L8744 from rfl,
    show L8750 ++ [F219] = L8746 from rfl] at h
  rw [i5161 hinj, i5159 hinj, i5160 hinj, i5162 hinj] at h
  linarith

theorem row1823 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8751 + (1 : ℝ) * HLm Γ 5 L8753 + (-1 : ℝ) * HLm Γ 5 L8755 + (-1 : ℝ) * HLm Γ 5 L8757 := by
  have h := HLm_submod hΓ [F0] L8758 [F67]
  rw [show [F0] ++ L8758 ++ [F67] = L8756 from rfl, show [F0] ++ L8758 = L8752 from rfl,
    show L8758 ++ [F67] = L8754 from rfl] at h
  rw [i5165 hinj, i5163 hinj, i5164 hinj, i5166 hinj] at h
  linarith

theorem row1824 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8759 + (1 : ℝ) * HLm Γ 5 L7397 + (-1 : ℝ) * HLm Γ 5 L8762 + (-1 : ℝ) * HLm Γ 5 L7393 := by
  have h := HLm_submod hΓ [F9] L8764 [F218]
  rw [show [F9] ++ L8764 ++ [F218] = L8763 from rfl, show [F9] ++ L8764 = L8760 from rfl,
    show L8764 ++ [F218] = L8761 from rfl] at h
  rw [i5169 hinj, i5167 hinj, i5168 hinj, i5170 hinj] at h
  linarith

theorem row1825 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8765 + (1 : ℝ) * HLm Γ 5 L7409 + (-1 : ℝ) * HLm Γ 5 L8768 + (-1 : ℝ) * HLm Γ 5 L7407 := by
  have h := HLm_submod hΓ [F16] L7408 [F67]
  rw [show [F16] ++ L7408 ++ [F67] = L8769 from rfl, show [F16] ++ L7408 = L8766 from rfl,
    show L7408 ++ [F67] = L8767 from rfl] at h
  rw [i5173 hinj, i5171 hinj, i5172 hinj, i4388 hinj] at h
  linarith

theorem row1826 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8770 + (1 : ℝ) * HLm Γ 5 L8772 + (-1 : ℝ) * HLm Γ 5 L8774 + (-1 : ℝ) * HLm Γ 5 L7990 := by
  have h := HLm_submod hΓ [F5] L7991 [F210]
  rw [show [F5] ++ L7991 ++ [F210] = L8775 from rfl, show [F5] ++ L7991 = L8771 from rfl,
    show L7991 ++ [F210] = L8773 from rfl] at h
  rw [i5176 hinj, i5174 hinj, i5175 hinj, i4711 hinj] at h
  linarith

theorem row1827 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8019 + (1 : ℝ) * HLm Γ 5 L8777 + (-1 : ℝ) * HLm Γ 5 L8779 + (-1 : ℝ) * HLm Γ 5 L2885 := by
  have h := HLm_submod hΓ [F210] L2885 [F27]
  rw [show [F210] ++ L2885 ++ [F27] = L8780 from rfl, show [F210] ++ L2885 = L8776 from rfl,
    show L2885 ++ [F27] = L8778 from rfl] at h
  rw [i5179 hinj, i5177 hinj, i5178 hinj] at h
  linarith

theorem row1828 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L851 + (1 : ℝ) * HLm Γ 5 L2293 + (-1 : ℝ) * HLm Γ 5 L842 + (-1 : ℝ) * HLm Γ 5 L2290 := by
  have h := HLm_submod hΓ [F0] L2630 [F45]
  rw [show [F0] ++ L2630 ++ [F45] = L8782 from rfl, show [F0] ++ L2630 = L2626 from rfl,
    show L2630 ++ [F45] = L8781 from rfl] at h
  rw [i5181 hinj, i1471 hinj, i5180 hinj, i1474 hinj] at h
  linarith

theorem row1829 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8783 + (1 : ℝ) * HLm Γ 5 L8785 + (-1 : ℝ) * HLm Γ 5 L8787 + (-1 : ℝ) * HLm Γ 5 L8789 := by
  have h := HLm_submod hΓ [F16] L8790 [F228]
  rw [show [F16] ++ L8790 ++ [F228] = L8788 from rfl, show [F16] ++ L8790 = L8784 from rfl,
    show L8790 ++ [F228] = L8786 from rfl] at h
  rw [i5184 hinj, i5182 hinj, i5183 hinj, i5185 hinj] at h
  linarith

theorem row1830 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8791 + (1 : ℝ) * HLm Γ 5 L8793 + (-1 : ℝ) * HLm Γ 5 L8795 + (-1 : ℝ) * HLm Γ 5 L8797 := by
  have h := HLm_submod hΓ [F25] L8798 [F45]
  rw [show [F25] ++ L8798 ++ [F45] = L8796 from rfl, show [F25] ++ L8798 = L8792 from rfl,
    show L8798 ++ [F45] = L8794 from rfl] at h
  rw [i5188 hinj, i5186 hinj, i5187 hinj, i5189 hinj] at h
  linarith

theorem row1831 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L851 + (1 : ℝ) * HLm Γ 5 L7590 + (-1 : ℝ) * HLm Γ 5 L3517 + (-1 : ℝ) * HLm Γ 5 L1506 := by
  have h := HLm_submod hΓ [F0] L1507 [F218]
  rw [show [F0] ++ L1507 ++ [F218] = L8801 from rfl, show [F0] ++ L1507 = L8799 from rfl,
    show L1507 ++ [F218] = L8800 from rfl] at h
  rw [i5192 hinj, i5190 hinj, i5191 hinj, i763 hinj] at h
  linarith

theorem row1832 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8802 + (1 : ℝ) * HLm Γ 5 L8804 + (-1 : ℝ) * HLm Γ 5 L8806 + (-1 : ℝ) * HLm Γ 5 L3455 := by
  have h := HLm_submod hΓ [F16] L3456 [F228]
  rw [show [F16] ++ L3456 ++ [F228] = L8807 from rfl, show [F16] ++ L3456 = L8803 from rfl,
    show L3456 ++ [F228] = L8805 from rfl] at h
  rw [i5195 hinj, i5193 hinj, i5194 hinj, i1939 hinj] at h
  linarith

theorem row1833 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7428 + (1 : ℝ) * HLm Γ 5 L5988 + (-1 : ℝ) * HLm Γ 5 L5982 + (-1 : ℝ) * HLm Γ 5 L7426 := by
  have h := HLm_submod hΓ [F7] L7427 [F16]
  rw [show [F7] ++ L7427 ++ [F16] = L8809 from rfl, show [F7] ++ L7427 = L7429 from rfl,
    show L7427 ++ [F16] = L8808 from rfl] at h
  rw [i5197 hinj, i4399 hinj, i5196 hinj, i4398 hinj] at h
  linarith

theorem row1834 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8810 + (1 : ℝ) * HLm Γ 5 L8812 + (-1 : ℝ) * HLm Γ 5 L8814 + (-1 : ℝ) * HLm Γ 5 L7433 := by
  have h := HLm_submod hΓ [F210] L7433 [F25]
  rw [show [F210] ++ L7433 ++ [F25] = L8815 from rfl, show [F210] ++ L7433 = L8811 from rfl,
    show L7433 ++ [F25] = L8813 from rfl] at h
  rw [i5200 hinj, i5198 hinj, i5199 hinj] at h
  linarith

theorem row1835 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8816 + (1 : ℝ) * HLm Γ 5 L7500 + (-1 : ℝ) * HLm Γ 5 L8819 + (-1 : ℝ) * HLm Γ 5 L8821 := by
  have h := HLm_submod hΓ [F90] L8822 [F219]
  rw [show [F90] ++ L8822 ++ [F219] = L8820 from rfl, show [F90] ++ L8822 = L8817 from rfl,
    show L8822 ++ [F219] = L8818 from rfl] at h
  rw [i5203 hinj, i5201 hinj, i5202 hinj, i5204 hinj] at h
  linarith

theorem row1836 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8823 + (1 : ℝ) * HLm Γ 5 L4693 + (-1 : ℝ) * HLm Γ 5 L4695 + (-1 : ℝ) * HLm Γ 5 L7461 := by
  have h := HLm_submod hΓ [F7] L8826 [F218]
  rw [show [F7] ++ L8826 ++ [F218] = L8825 from rfl, show [F7] ++ L8826 = L8824 from rfl,
    show L8826 ++ [F218] = L6040 from rfl] at h
  rw [i5206 hinj, i5205 hinj, i3451 hinj, i5207 hinj] at h
  linarith

theorem row1837 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L731 + (1 : ℝ) * HLm Γ 5 L4686 + (-1 : ℝ) * HLm Γ 5 L4329 + (-1 : ℝ) * HLm Γ 5 L208 := by
  have h := HLm_submod hΓ [F0] L209 [F210]
  rw [show [F0] ++ L209 ++ [F210] = L8828 from rfl, show [F0] ++ L209 = L732 from rfl,
    show L209 ++ [F210] = L8827 from rfl] at h
  rw [i5209 hinj, i321 hinj, i5208 hinj, i73 hinj] at h
  linarith

theorem row1838 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8829 + (1 : ℝ) * HLm Γ 5 L8831 + (-1 : ℝ) * HLm Γ 5 L8833 + (-1 : ℝ) * HLm Γ 5 L8835 := by
  have h := HLm_submod hΓ [F210] L8836 [F90]
  rw [show [F210] ++ L8836 ++ [F90] = L8834 from rfl, show [F210] ++ L8836 = L8830 from rfl,
    show L8836 ++ [F90] = L8832 from rfl] at h
  rw [i5212 hinj, i5210 hinj, i5211 hinj, i5213 hinj] at h
  linarith

theorem row1839 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8837 + (1 : ℝ) * HLm Γ 5 L8839 + (-1 : ℝ) * HLm Γ 5 L8841 + (-1 : ℝ) * HLm Γ 5 L8843 := by
  have h := HLm_submod hΓ [F46] L8844 [F211]
  rw [show [F46] ++ L8844 ++ [F211] = L8842 from rfl, show [F46] ++ L8844 = L8838 from rfl,
    show L8844 ++ [F211] = L8840 from rfl] at h
  rw [i5216 hinj, i5214 hinj, i5215 hinj, i5217 hinj] at h
  linarith

theorem row1840 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8845 + (1 : ℝ) * HLm Γ 5 L8847 + (-1 : ℝ) * HLm Γ 5 L8849 + (-1 : ℝ) * HLm Γ 5 L8851 := by
  have h := HLm_submod hΓ [F46] L8852 [F211]
  rw [show [F46] ++ L8852 ++ [F211] = L8850 from rfl, show [F46] ++ L8852 = L8846 from rfl,
    show L8852 ++ [F211] = L8848 from rfl] at h
  rw [i5220 hinj, i5218 hinj, i5219 hinj, i5221 hinj] at h
  linarith

theorem row1841 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1710 + (1 : ℝ) * HLm Γ 5 L7490 + (-1 : ℝ) * HLm Γ 5 L8855 + (-1 : ℝ) * HLm Γ 5 L7486 := by
  have h := HLm_submod hΓ [F7] L8857 [F214]
  rw [show [F7] ++ L8857 ++ [F214] = L8856 from rfl, show [F7] ++ L8857 = L8853 from rfl,
    show L8857 ++ [F214] = L8854 from rfl] at h
  rw [i5224 hinj, i5222 hinj, i5223 hinj, i5225 hinj] at h
  linarith

theorem row1842 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8858 + (1 : ℝ) * HLm Γ 5 L8860 + (-1 : ℝ) * HLm Γ 5 L8862 + (-1 : ℝ) * HLm Γ 5 L7449 := by
  have h := HLm_submod hΓ [F210] L8864 [F85]
  rw [show [F210] ++ L8864 ++ [F85] = L8863 from rfl, show [F210] ++ L8864 = L8859 from rfl,
    show L8864 ++ [F85] = L8861 from rfl] at h
  rw [i5228 hinj, i5226 hinj, i5227 hinj, i5229 hinj] at h
  linarith

theorem row1843 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7445 + (1 : ℝ) * HLm Γ 5 L8866 + (-1 : ℝ) * HLm Γ 5 L8868 + (-1 : ℝ) * HLm Γ 5 L7443 := by
  have h := HLm_submod hΓ [F46] L8870 [F16]
  rw [show [F46] ++ L8870 ++ [F16] = L8869 from rfl, show [F46] ++ L8870 = L8865 from rfl,
    show L8870 ++ [F16] = L8867 from rfl] at h
  rw [i5232 hinj, i5230 hinj, i5231 hinj, i5233 hinj] at h
  linarith

theorem row1844 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7453 + (1 : ℝ) * HLm Γ 5 L8871 + (-1 : ℝ) * HLm Γ 5 L8873 + (-1 : ℝ) * HLm Γ 5 L7451 := by
  have h := HLm_submod hΓ [F67] L7452 [F214]
  rw [show [F67] ++ L7452 ++ [F214] = L8874 from rfl, show [F67] ++ L7452 = L7454 from rfl,
    show L7452 ++ [F214] = L8872 from rfl] at h
  rw [i5235 hinj, i4412 hinj, i5234 hinj, i4411 hinj] at h
  linarith

theorem row1845 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8875 + (1 : ℝ) * HLm Γ 5 L8877 + (-1 : ℝ) * HLm Γ 5 L8879 + (-1 : ℝ) * HLm Γ 5 L7482 := by
  have h := HLm_submod hΓ [F210] L7482 [F96]
  rw [show [F210] ++ L7482 ++ [F96] = L8880 from rfl, show [F210] ++ L7482 = L8876 from rfl,
    show L7482 ++ [F96] = L8878 from rfl] at h
  rw [i5238 hinj, i5236 hinj, i5237 hinj] at h
  linarith

theorem row1846 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8783 + (1 : ℝ) * HLm Γ 5 L7459 + (-1 : ℝ) * HLm Γ 5 L8883 + (-1 : ℝ) * HLm Γ 5 L7457 := by
  have h := HLm_submod hΓ [F9] L7458 [F214]
  rw [show [F9] ++ L7458 ++ [F214] = L8884 from rfl, show [F9] ++ L7458 = L8881 from rfl,
    show L7458 ++ [F214] = L8882 from rfl] at h
  rw [i5241 hinj, i5239 hinj, i5240 hinj, i4414 hinj] at h
  linarith

theorem row1847 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8885 + (1 : ℝ) * HLm Γ 5 L7469 + (-1 : ℝ) * HLm Γ 5 L4736 + (-1 : ℝ) * HLm Γ 5 L7467 := by
  have h := HLm_submod hΓ [F9] L8889 [F67]
  rw [show [F9] ++ L8889 ++ [F67] = L8888 from rfl, show [F9] ++ L8889 = L8886 from rfl,
    show L8889 ++ [F67] = L8887 from rfl] at h
  rw [i5244 hinj, i5242 hinj, i5243 hinj, i5245 hinj] at h
  linarith

theorem row1848 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4688 + (1 : ℝ) * HLm Γ 5 L7475 + (-1 : ℝ) * HLm Γ 5 L4690 + (-1 : ℝ) * HLm Γ 5 L7473 := by
  have h := HLm_submod hΓ [F46] L8893 [F210]
  rw [show [F46] ++ L8893 ++ [F210] = L8892 from rfl, show [F46] ++ L8893 = L8890 from rfl,
    show L8893 ++ [F210] = L8891 from rfl] at h
  rw [i5248 hinj, i5246 hinj, i5247 hinj, i5249 hinj] at h
  linarith

theorem row1849 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3316 + (1 : ℝ) * HLm Γ 5 L7724 + (-1 : ℝ) * HLm Γ 5 L8896 + (-1 : ℝ) * HLm Γ 5 L8898 := by
  have h := HLm_submod hΓ [F0] L8899 [F6]
  rw [show [F0] ++ L8899 ++ [F6] = L8897 from rfl, show [F0] ++ L8899 = L8894 from rfl,
    show L8899 ++ [F6] = L8895 from rfl] at h
  rw [i5252 hinj, i5250 hinj, i5251 hinj, i5253 hinj] at h
  linarith

theorem row1850 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L845 + (1 : ℝ) * HLm Γ 5 L8901 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L3521 := by
  have h := HLm_submod hΓ [F0] L3522 [F25]
  rw [show [F0] ++ L3522 ++ [F25] = L8903 from rfl, show [F0] ++ L3522 = L8900 from rfl,
    show L3522 ++ [F25] = L8902 from rfl] at h
  rw [i5256 hinj, i5254 hinj, i5255 hinj, i1975 hinj] at h
  linarith

theorem row1851 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2241 + (1 : ℝ) * HLm Γ 5 L8905 + (-1 : ℝ) * HLm Γ 5 L4429 + (-1 : ℝ) * HLm Γ 5 L162 := by
  have h := HLm_submod hΓ [F0] L8908 [F214]
  rw [show [F0] ++ L8908 ++ [F214] = L8907 from rfl, show [F0] ++ L8908 = L8904 from rfl,
    show L8908 ++ [F214] = L8906 from rfl] at h
  rw [i5259 hinj, i5257 hinj, i5258 hinj, i5260 hinj] at h
  linarith

theorem row1852 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2241 + (1 : ℝ) * HLm Γ 5 L7563 + (-1 : ℝ) * HLm Γ 5 L4818 + (-1 : ℝ) * HLm Γ 5 L7561 := by
  have h := HLm_submod hΓ [F0] L8912 [F210]
  rw [show [F0] ++ L8912 ++ [F210] = L8911 from rfl, show [F0] ++ L8912 = L8909 from rfl,
    show L8912 ++ [F210] = L8910 from rfl] at h
  rw [i5263 hinj, i5261 hinj, i5262 hinj, i5264 hinj] at h
  linarith

theorem row1853 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8913 + (1 : ℝ) * HLm Γ 5 L4785 + (-1 : ℝ) * HLm Γ 5 L8915 + (-1 : ℝ) * HLm Γ 5 L4789 := by
  have h := HLm_submod hΓ [F3] L4790 [F228]
  rw [show [F3] ++ L4790 ++ [F228] = L8916 from rfl, show [F3] ++ L4790 = L8914 from rfl,
    show L4790 ++ [F228] = L4786 from rfl] at h
  rw [i5266 hinj, i5265 hinj, i2691 hinj, i2693 hinj] at h
  linarith

theorem row1854 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8917 + (1 : ℝ) * HLm Γ 5 L8919 + (-1 : ℝ) * HLm Γ 5 L8921 + (-1 : ℝ) * HLm Γ 5 L1566 := by
  have h := HLm_submod hΓ [F210] L1566 [F86]
  rw [show [F210] ++ L1566 ++ [F86] = L8922 from rfl, show [F210] ++ L1566 = L8918 from rfl,
    show L1566 ++ [F86] = L8920 from rfl] at h
  rw [i5269 hinj, i5267 hinj, i5268 hinj] at h
  linarith

theorem row1855 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8923 + (1 : ℝ) * HLm Γ 5 L8925 + (-1 : ℝ) * HLm Γ 5 L8927 + (-1 : ℝ) * HLm Γ 5 L8929 := by
  have h := HLm_submod hΓ [F3] L8930 [F211]
  rw [show [F3] ++ L8930 ++ [F211] = L8928 from rfl, show [F3] ++ L8930 = L8924 from rfl,
    show L8930 ++ [F211] = L8926 from rfl] at h
  rw [i5272 hinj, i5270 hinj, i5271 hinj, i5273 hinj] at h
  linarith

theorem row1856 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2338 + (1 : ℝ) * HLm Γ 5 L8932 + (-1 : ℝ) * HLm Γ 5 L8934 + (-1 : ℝ) * HLm Γ 5 L2336 := by
  have h := HLm_submod hΓ [F0] L2336 [F82]
  rw [show [F0] ++ L2336 ++ [F82] = L8935 from rfl, show [F0] ++ L2336 = L8931 from rfl,
    show L2336 ++ [F82] = L8933 from rfl] at h
  rw [i5276 hinj, i5274 hinj, i5275 hinj] at h
  linarith

theorem row1857 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8936 + (1 : ℝ) * HLm Γ 5 L5287 + (-1 : ℝ) * HLm Γ 5 L5289 + (-1 : ℝ) * HLm Γ 5 L3541 := by
  have h := HLm_submod hΓ [F2] L8940 [F228]
  rw [show [F2] ++ L8940 ++ [F228] = L8939 from rfl, show [F2] ++ L8940 = L8937 from rfl,
    show L8940 ++ [F228] = L8938 from rfl] at h
  rw [i5279 hinj, i5277 hinj, i5278 hinj, i5280 hinj] at h
  linarith

theorem row1858 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8936 + (1 : ℝ) * HLm Γ 5 L8941 + (-1 : ℝ) * HLm Γ 5 L8943 + (-1 : ℝ) * HLm Γ 5 L3541 := by
  have h := HLm_submod hΓ [F2] L8940 [F217]
  rw [show [F2] ++ L8940 ++ [F217] = L8944 from rfl, show [F2] ++ L8940 = L8937 from rfl,
    show L8940 ++ [F217] = L8942 from rfl] at h
  rw [i5282 hinj, i5277 hinj, i5281 hinj, i5280 hinj] at h
  linarith

theorem row1859 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8945 + (1 : ℝ) * HLm Γ 5 L8947 + (-1 : ℝ) * HLm Γ 5 L8949 + (-1 : ℝ) * HLm Γ 5 L3552 := by
  have h := HLm_submod hΓ [F2] L8951 [F218]
  rw [show [F2] ++ L8951 ++ [F218] = L8950 from rfl, show [F2] ++ L8951 = L8946 from rfl,
    show L8951 ++ [F218] = L8948 from rfl] at h
  rw [i5285 hinj, i5283 hinj, i5284 hinj, i5286 hinj] at h
  linarith

theorem row1860 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8952 + (1 : ℝ) * HLm Γ 5 L8954 + (-1 : ℝ) * HLm Γ 5 L8956 + (-1 : ℝ) * HLm Γ 5 L7516 := by
  have h := HLm_submod hΓ [F67] L7517 [F86]
  rw [show [F67] ++ L7517 ++ [F86] = L8957 from rfl, show [F67] ++ L7517 = L8953 from rfl,
    show L7517 ++ [F86] = L8955 from rfl] at h
  rw [i5289 hinj, i5287 hinj, i5288 hinj, i4449 hinj] at h
  linarith

theorem row1861 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L338 + (1 : ℝ) * HLm Γ 5 L7539 + (-1 : ℝ) * HLm Γ 5 L4835 + (-1 : ℝ) * HLm Γ 5 L7535 := by
  have h := HLm_submod hΓ [F0] L8961 [F214]
  rw [show [F0] ++ L8961 ++ [F214] = L8960 from rfl, show [F0] ++ L8961 = L8958 from rfl,
    show L8961 ++ [F214] = L8959 from rfl] at h
  rw [i5292 hinj, i5290 hinj, i5291 hinj, i5293 hinj] at h
  linarith

theorem row1862 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1458 + (1 : ℝ) * HLm Γ 5 L8962 + (-1 : ℝ) * HLm Γ 5 L1614 + (-1 : ℝ) * HLm Γ 5 L7526 := by
  have h := HLm_submod hΓ [F0] L7527 [F1]
  rw [show [F0] ++ L7527 ++ [F1] = L8964 from rfl, show [F0] ++ L7527 = L7528 from rfl,
    show L7527 ++ [F1] = L8963 from rfl] at h
  rw [i5295 hinj, i4456 hinj, i5294 hinj, i4455 hinj] at h
  linarith

theorem row1863 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8965 + (1 : ℝ) * HLm Γ 5 L8967 + (-1 : ℝ) * HLm Γ 5 L8969 + (-1 : ℝ) * HLm Γ 5 L2329 := by
  have h := HLm_submod hΓ [F210] L4858 [F30]
  rw [show [F210] ++ L4858 ++ [F30] = L8970 from rfl, show [F210] ++ L4858 = L8966 from rfl,
    show L4858 ++ [F30] = L8968 from rfl] at h
  rw [i5298 hinj, i5296 hinj, i5297 hinj, i2735 hinj] at h
  linarith

theorem row1864 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8971 + (1 : ℝ) * HLm Γ 5 L8973 + (-1 : ℝ) * HLm Γ 5 L8975 + (-1 : ℝ) * HLm Γ 5 L4024 := by
  have h := HLm_submod hΓ [F228] L4025 [F96]
  rw [show [F228] ++ L4025 ++ [F96] = L8976 from rfl, show [F228] ++ L4025 = L8972 from rfl,
    show L4025 ++ [F96] = L8974 from rfl] at h
  rw [i5301 hinj, i5299 hinj, i5300 hinj, i2246 hinj] at h
  linarith

theorem row1865 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8977 + (1 : ℝ) * HLm Γ 5 L8979 + (-1 : ℝ) * HLm Γ 5 L4298 + (-1 : ℝ) * HLm Γ 5 L8982 := by
  have h := HLm_submod hΓ [F0] L8983 [F6]
  rw [show [F0] ++ L8983 ++ [F6] = L8981 from rfl, show [F0] ++ L8983 = L8978 from rfl,
    show L8983 ++ [F6] = L8980 from rfl] at h
  rw [i5304 hinj, i5302 hinj, i5303 hinj, i5305 hinj] at h
  linarith

theorem row1866 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8984 + (1 : ℝ) * HLm Γ 5 L8986 + (-1 : ℝ) * HLm Γ 5 L4882 + (-1 : ℝ) * HLm Γ 5 L8989 := by
  have h := HLm_submod hΓ [F0] L8990 [F45]
  rw [show [F0] ++ L8990 ++ [F45] = L8988 from rfl, show [F0] ++ L8990 = L8985 from rfl,
    show L8990 ++ [F45] = L8987 from rfl] at h
  rw [i5308 hinj, i5306 hinj, i5307 hinj, i5309 hinj] at h
  linarith

theorem row1867 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8991 + (1 : ℝ) * HLm Γ 5 L8993 + (-1 : ℝ) * HLm Γ 5 L8995 + (-1 : ℝ) * HLm Γ 5 L4050 := by
  have h := HLm_submod hΓ [F0] L4051 [F43]
  rw [show [F0] ++ L4051 ++ [F43] = L8996 from rfl, show [F0] ++ L4051 = L8992 from rfl,
    show L4051 ++ [F43] = L8994 from rfl] at h
  rw [i5312 hinj, i5310 hinj, i5311 hinj, i2260 hinj] at h
  linarith

theorem row1868 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3442 + (1 : ℝ) * HLm Γ 5 L1606 + (-1 : ℝ) * HLm Γ 5 L2658 + (-1 : ℝ) * HLm Γ 5 L1610 := by
  have h := HLm_submod hΓ [F51] L1611 [F16]
  rw [show [F51] ++ L1611 ++ [F16] = L8998 from rfl, show [F51] ++ L1611 = L8997 from rfl,
    show L1611 ++ [F16] = L1607 from rfl] at h
  rw [i5314 hinj, i5313 hinj, i825 hinj, i827 hinj] at h
  linarith

theorem row1869 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8049 + (1 : ℝ) * HLm Γ 5 L9000 + (-1 : ℝ) * HLm Γ 5 L9002 + (-1 : ℝ) * HLm Γ 5 L8046 := by
  have h := HLm_submod hΓ [F108] L8047 [F67]
  rw [show [F108] ++ L8047 ++ [F67] = L9003 from rfl, show [F108] ++ L8047 = L8999 from rfl,
    show L8047 ++ [F67] = L9001 from rfl] at h
  rw [i5317 hinj, i5315 hinj, i5316 hinj, i4744 hinj] at h
  linarith

theorem row1870 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7545 + (1 : ℝ) * HLm Γ 5 L9004 + (-1 : ℝ) * HLm Γ 5 L9006 + (-1 : ℝ) * HLm Γ 5 L7543 := by
  have h := HLm_submod hΓ [F1] L7544 [F67]
  rw [show [F1] ++ L7544 ++ [F67] = L9007 from rfl, show [F1] ++ L7544 = L7546 from rfl,
    show L7544 ++ [F67] = L9005 from rfl] at h
  rw [i5319 hinj, i4465 hinj, i5318 hinj, i4464 hinj] at h
  linarith

theorem row1871 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L788 + (1 : ℝ) * HLm Γ 5 L9009 + (-1 : ℝ) * HLm Γ 5 L9011 + (-1 : ℝ) * HLm Γ 5 L786 := by
  have h := HLm_submod hΓ [F0] L1621 [F218]
  rw [show [F0] ++ L1621 ++ [F218] = L9012 from rfl, show [F0] ++ L1621 = L9008 from rfl,
    show L1621 ++ [F218] = L9010 from rfl] at h
  rw [i5322 hinj, i5320 hinj, i5321 hinj, i834 hinj] at h
  linarith

theorem row1872 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7306 + (1 : ℝ) * HLm Γ 5 L9013 + (-1 : ℝ) * HLm Γ 5 L9015 + (-1 : ℝ) * HLm Γ 5 L7547 := by
  have h := HLm_submod hΓ [F0] L7548 [F218]
  rw [show [F0] ++ L7548 ++ [F218] = L9016 from rfl, show [F0] ++ L7548 = L7549 from rfl,
    show L7548 ++ [F218] = L9014 from rfl] at h
  rw [i5324 hinj, i4467 hinj, i5323 hinj, i4466 hinj] at h
  linarith

theorem row1873 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1524 + (1 : ℝ) * HLm Γ 5 L9018 + (-1 : ℝ) * HLm Γ 5 L9020 + (-1 : ℝ) * HLm Γ 5 L1630 := by
  have h := HLm_submod hΓ [F2] L9022 [F210]
  rw [show [F2] ++ L9022 ++ [F210] = L9021 from rfl, show [F2] ++ L9022 = L9017 from rfl,
    show L9022 ++ [F210] = L9019 from rfl] at h
  rw [i5327 hinj, i5325 hinj, i5326 hinj, i5328 hinj] at h
  linarith

theorem row1874 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9023 + (1 : ℝ) * HLm Γ 5 L9025 + (-1 : ℝ) * HLm Γ 5 L9027 + (-1 : ℝ) * HLm Γ 5 L9029 := by
  have h := HLm_submod hΓ [F210] L9030 [F43]
  rw [show [F210] ++ L9030 ++ [F43] = L9028 from rfl, show [F210] ++ L9030 = L9024 from rfl,
    show L9030 ++ [F43] = L9026 from rfl] at h
  rw [i5331 hinj, i5329 hinj, i5330 hinj, i5332 hinj] at h
  linarith

theorem row1875 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9031 + (1 : ℝ) * HLm Γ 5 L9033 + (-1 : ℝ) * HLm Γ 5 L9035 + (-1 : ℝ) * HLm Γ 5 L868 := by
  have h := HLm_submod hΓ [F107] L869 [F210]
  rw [show [F107] ++ L869 ++ [F210] = L9036 from rfl, show [F107] ++ L869 = L9032 from rfl,
    show L869 ++ [F210] = L9034 from rfl] at h
  rw [i5335 hinj, i5333 hinj, i5334 hinj, i395 hinj] at h
  linarith

theorem row1876 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4974 + (1 : ℝ) * HLm Γ 5 L9038 + (-1 : ℝ) * HLm Γ 5 L9040 + (-1 : ℝ) * HLm Γ 5 L4172 := by
  have h := HLm_submod hΓ [F67] L4978 [F17]
  rw [show [F67] ++ L4978 ++ [F17] = L9041 from rfl, show [F67] ++ L4978 = L9037 from rfl,
    show L4978 ++ [F17] = L9039 from rfl] at h
  rw [i5338 hinj, i5336 hinj, i5337 hinj, i2806 hinj] at h
  linarith

theorem row1877 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3648 + (1 : ℝ) * HLm Γ 5 L9042 + (-1 : ℝ) * HLm Γ 5 L9044 + (-1 : ℝ) * HLm Γ 5 L3646 := by
  have h := HLm_submod hΓ [F7] L3647 [F16]
  rw [show [F7] ++ L3647 ++ [F16] = L9045 from rfl, show [F7] ++ L3647 = L3649 from rfl,
    show L3647 ++ [F16] = L9043 from rfl] at h
  rw [i5340 hinj, i2043 hinj, i5339 hinj, i2042 hinj] at h
  linarith

theorem row1878 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3656 + (1 : ℝ) * HLm Γ 5 L7574 + (-1 : ℝ) * HLm Γ 5 L9048 + (-1 : ℝ) * HLm Γ 5 L3654 := by
  have h := HLm_submod hΓ [F16] L3654 [F25]
  rw [show [F16] ++ L3654 ++ [F25] = L9049 from rfl, show [F16] ++ L3654 = L9046 from rfl,
    show L3654 ++ [F25] = L9047 from rfl] at h
  rw [i5343 hinj, i5341 hinj, i5342 hinj] at h
  linarith

theorem row1879 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3314 + (1 : ℝ) * HLm Γ 5 L7581 + (-1 : ℝ) * HLm Γ 5 L4425 + (-1 : ℝ) * HLm Γ 5 L7579 := by
  have h := HLm_submod hΓ [F7] L9053 [F16]
  rw [show [F7] ++ L9053 ++ [F16] = L9052 from rfl, show [F7] ++ L9053 = L9050 from rfl,
    show L9053 ++ [F16] = L9051 from rfl] at h
  rw [i5346 hinj, i5344 hinj, i5345 hinj, i5347 hinj] at h
  linarith

theorem row1880 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4124 + (1 : ℝ) * HLm Γ 5 L9055 + (-1 : ℝ) * HLm Γ 5 L9057 + (-1 : ℝ) * HLm Γ 5 L918 := by
  have h := HLm_submod hΓ [F67] L9059 [F36]
  rw [show [F67] ++ L9059 ++ [F36] = L9058 from rfl, show [F67] ++ L9059 = L9054 from rfl,
    show L9059 ++ [F36] = L9056 from rfl] at h
  rw [i5350 hinj, i5348 hinj, i5349 hinj, i5351 hinj] at h
  linarith

theorem row1881 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1187 + (1 : ℝ) * HLm Γ 5 L7587 + (-1 : ℝ) * HLm Γ 5 L9062 + (-1 : ℝ) * HLm Γ 5 L7585 := by
  have h := HLm_submod hΓ [F3] L7586 [F210]
  rw [show [F3] ++ L7586 ++ [F210] = L9063 from rfl, show [F3] ++ L7586 = L9060 from rfl,
    show L7586 ++ [F210] = L9061 from rfl] at h
  rw [i5354 hinj, i5352 hinj, i5353 hinj, i4488 hinj] at h
  linarith

theorem row1882 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9064 + (1 : ℝ) * HLm Γ 5 L9066 + (-1 : ℝ) * HLm Γ 5 L9068 + (-1 : ℝ) * HLm Γ 5 L7779 := by
  have h := HLm_submod hΓ [F210] L9070 [F36]
  rw [show [F210] ++ L9070 ++ [F36] = L9069 from rfl, show [F210] ++ L9070 = L9065 from rfl,
    show L9070 ++ [F36] = L9067 from rfl] at h
  rw [i5357 hinj, i5355 hinj, i5356 hinj, i5358 hinj] at h
  linarith

theorem row1883 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9071 + (1 : ℝ) * HLm Γ 5 L7850 + (-1 : ℝ) * HLm Γ 5 L9074 + (-1 : ℝ) * HLm Γ 5 L7846 := by
  have h := HLm_submod hΓ [F1] L9076 [F210]
  rw [show [F1] ++ L9076 ++ [F210] = L9075 from rfl, show [F1] ++ L9076 = L9072 from rfl,
    show L9076 ++ [F210] = L9073 from rfl] at h
  rw [i5361 hinj, i5359 hinj, i5360 hinj, i5362 hinj] at h
  linarith

theorem row1884 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L260 + (1 : ℝ) * HLm Γ 5 L7668 + (-1 : ℝ) * HLm Γ 5 L1894 + (-1 : ℝ) * HLm Γ 5 L7665 := by
  have h := HLm_submod hΓ [F0] L7666 [F67]
  rw [show [F0] ++ L7666 ++ [F67] = L9078 from rfl, show [F0] ++ L7666 = L9077 from rfl,
    show L7666 ++ [F67] = L7669 from rfl] at h
  rw [i5364 hinj, i5363 hinj, i4536 hinj, i4534 hinj] at h
  linarith

theorem row1885 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9079 + (1 : ℝ) * HLm Γ 5 L9081 + (-1 : ℝ) * HLm Γ 5 L9083 + (-1 : ℝ) * HLm Γ 5 L7722 := by
  have h := HLm_submod hΓ [F210] L9085 [F27]
  rw [show [F210] ++ L9085 ++ [F27] = L9084 from rfl, show [F210] ++ L9085 = L9080 from rfl,
    show L9085 ++ [F27] = L9082 from rfl] at h
  rw [i5367 hinj, i5365 hinj, i5366 hinj, i5368 hinj] at h
  linarith

theorem row1886 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9086 + (1 : ℝ) * HLm Γ 5 L9088 + (-1 : ℝ) * HLm Γ 5 L9090 + (-1 : ℝ) * HLm Γ 5 L3823 := by
  have h := HLm_submod hΓ [F7] L3824 [F6]
  rw [show [F7] ++ L3824 ++ [F6] = L9091 from rfl, show [F7] ++ L3824 = L9087 from rfl,
    show L3824 ++ [F6] = L9089 from rfl] at h
  rw [i5371 hinj, i5369 hinj, i5370 hinj, i2136 hinj] at h
  linarith

theorem row1887 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7610 + (1 : ℝ) * HLm Γ 5 L9093 + (-1 : ℝ) * HLm Γ 5 L9095 + (-1 : ℝ) * HLm Γ 5 L7608 := by
  have h := HLm_submod hΓ [F7] L9097 [F67]
  rw [show [F7] ++ L9097 ++ [F67] = L9096 from rfl, show [F7] ++ L9097 = L9092 from rfl,
    show L9097 ++ [F67] = L9094 from rfl] at h
  rw [i5374 hinj, i5372 hinj, i5373 hinj, i5375 hinj] at h
  linarith

theorem row1888 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9098 + (1 : ℝ) * HLm Γ 5 L9100 + (-1 : ℝ) * HLm Γ 5 L9102 + (-1 : ℝ) * HLm Γ 5 L1027 := by
  have h := HLm_submod hΓ [F211] L9104 [F45]
  rw [show [F211] ++ L9104 ++ [F45] = L9103 from rfl, show [F211] ++ L9104 = L9099 from rfl,
    show L9104 ++ [F45] = L9101 from rfl] at h
  rw [i5378 hinj, i5376 hinj, i5377 hinj, i5379 hinj] at h
  linarith

theorem row1889 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4667 + (1 : ℝ) * HLm Γ 5 L9106 + (-1 : ℝ) * HLm Γ 5 L4669 + (-1 : ℝ) * HLm Γ 5 L2468 := by
  have h := HLm_submod hΓ [F47] L9109 [F210]
  rw [show [F47] ++ L9109 ++ [F210] = L9108 from rfl, show [F47] ++ L9109 = L9105 from rfl,
    show L9109 ++ [F210] = L9107 from rfl] at h
  rw [i5382 hinj, i5380 hinj, i5381 hinj, i5383 hinj] at h
  linarith

theorem row1890 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9110 + (1 : ℝ) * HLm Γ 5 L5030 + (-1 : ℝ) * HLm Γ 5 L9112 + (-1 : ℝ) * HLm Γ 5 L3694 := by
  have h := HLm_submod hΓ [F52] L3695 [F210]
  rw [show [F52] ++ L3695 ++ [F210] = L9113 from rfl, show [F52] ++ L3695 = L9111 from rfl,
    show L3695 ++ [F210] = L5031 from rfl] at h
  rw [i5385 hinj, i5384 hinj, i2833 hinj, i2068 hinj] at h
  linarith

theorem row1891 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3763 + (1 : ℝ) * HLm Γ 5 L9115 + (-1 : ℝ) * HLm Γ 5 L9117 + (-1 : ℝ) * HLm Γ 5 L7593 := by
  have h := HLm_submod hΓ [F62] L9119 [F210]
  rw [show [F62] ++ L9119 ++ [F210] = L9118 from rfl, show [F62] ++ L9119 = L9114 from rfl,
    show L9119 ++ [F210] = L9116 from rfl] at h
  rw [i5388 hinj, i5386 hinj, i5387 hinj, i5389 hinj] at h
  linarith

theorem row1892 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3401 + (1 : ℝ) * HLm Γ 5 L9120 + (-1 : ℝ) * HLm Γ 5 L9122 + (-1 : ℝ) * HLm Γ 5 L7602 := by
  have h := HLm_submod hΓ [F7] L9124 [F16]
  rw [show [F7] ++ L9124 ++ [F16] = L9123 from rfl, show [F7] ++ L9124 = L4414 from rfl,
    show L9124 ++ [F16] = L9121 from rfl] at h
  rw [i5391 hinj, i2475 hinj, i5390 hinj, i5392 hinj] at h
  linarith

theorem row1893 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4362 + (1 : ℝ) * HLm Γ 5 L7599 + (-1 : ℝ) * HLm Γ 5 L9127 + (-1 : ℝ) * HLm Γ 5 L3725 := by
  have h := HLm_submod hΓ [F1] L5064 [F7]
  rw [show [F1] ++ L5064 ++ [F7] = L9128 from rfl, show [F1] ++ L5064 = L9125 from rfl,
    show L5064 ++ [F7] = L9126 from rfl] at h
  rw [i5395 hinj, i5393 hinj, i5394 hinj, i2852 hinj] at h
  linarith

theorem row1894 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5384 + (1 : ℝ) * HLm Γ 5 L7945 + (-1 : ℝ) * HLm Γ 5 L5381 + (-1 : ℝ) * HLm Γ 5 L7941 := by
  have h := HLm_submod hΓ [F10] L7942 [F45]
  rw [show [F10] ++ L7942 ++ [F45] = L9130 from rfl, show [F10] ++ L7942 = L9129 from rfl,
    show L7942 ++ [F45] = L7946 from rfl] at h
  rw [i5397 hinj, i5396 hinj, i4686 hinj, i4684 hinj] at h
  linarith

theorem row1895 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8170 + (1 : ℝ) * HLm Γ 5 L9132 + (-1 : ℝ) * HLm Γ 5 L9134 + (-1 : ℝ) * HLm Γ 5 L8115 := by
  have h := HLm_submod hΓ [F0] L9136 [F16]
  rw [show [F0] ++ L9136 ++ [F16] = L9135 from rfl, show [F0] ++ L9136 = L9131 from rfl,
    show L9136 ++ [F16] = L9133 from rfl] at h
  rw [i5400 hinj, i5398 hinj, i5399 hinj, i5401 hinj] at h
  linarith

theorem row1896 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9137 + (1 : ℝ) * HLm Γ 5 L9139 + (-1 : ℝ) * HLm Γ 5 L9141 + (-1 : ℝ) * HLm Γ 5 L2978 := by
  have h := HLm_submod hΓ [F1] L2979 [F67]
  rw [show [F1] ++ L2979 ++ [F67] = L9142 from rfl, show [F1] ++ L2979 = L9138 from rfl,
    show L2979 ++ [F67] = L9140 from rfl] at h
  rw [i5404 hinj, i5402 hinj, i5403 hinj, i1698 hinj] at h
  linarith

theorem row1897 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9143 + (1 : ℝ) * HLm Γ 5 L7630 + (-1 : ℝ) * HLm Γ 5 L9146 + (-1 : ℝ) * HLm Γ 5 L9148 := by
  have h := HLm_submod hΓ [F228] L9149 [F85]
  rw [show [F228] ++ L9149 ++ [F85] = L9147 from rfl, show [F228] ++ L9149 = L9144 from rfl,
    show L9149 ++ [F85] = L9145 from rfl] at h
  rw [i5407 hinj, i5405 hinj, i5406 hinj, i5408 hinj] at h
  linarith

theorem row1898 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9150 + (1 : ℝ) * HLm Γ 5 L9152 + (-1 : ℝ) * HLm Γ 5 L9154 + (-1 : ℝ) * HLm Γ 5 L9156 := by
  have h := HLm_submod hΓ [F228] L9157 [F85]
  rw [show [F228] ++ L9157 ++ [F85] = L9155 from rfl, show [F228] ++ L9157 = L9151 from rfl,
    show L9157 ++ [F85] = L9153 from rfl] at h
  rw [i5411 hinj, i5409 hinj, i5410 hinj, i5412 hinj] at h
  linarith

theorem row1899 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9158 + (1 : ℝ) * HLm Γ 5 L7644 + (-1 : ℝ) * HLm Γ 5 L9161 + (-1 : ℝ) * HLm Γ 5 L7642 := by
  have h := HLm_submod hΓ [F107] L9163 [F16]
  rw [show [F107] ++ L9163 ++ [F16] = L9162 from rfl, show [F107] ++ L9163 = L9159 from rfl,
    show L9163 ++ [F16] = L9160 from rfl] at h
  rw [i5415 hinj, i5413 hinj, i5414 hinj, i5416 hinj] at h
  linarith

theorem row1900 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7182 + (1 : ℝ) * HLm Γ 5 L8029 + (-1 : ℝ) * HLm Γ 5 L9165 + (-1 : ℝ) * HLm Γ 5 L8027 := by
  have h := HLm_submod hΓ [F0] L8028 [F16]
  rw [show [F0] ++ L8028 ++ [F16] = L9166 from rfl, show [F0] ++ L8028 = L9164 from rfl,
    show L8028 ++ [F16] = L8030 from rfl] at h
  rw [i5418 hinj, i5417 hinj, i4733 hinj, i4732 hinj] at h
  linarith

theorem row1901 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9167 + (1 : ℝ) * HLm Γ 5 L9169 + (-1 : ℝ) * HLm Γ 5 L9171 + (-1 : ℝ) * HLm Γ 5 L9173 := by
  have h := HLm_submod hΓ [F51] L9174 [F219]
  rw [show [F51] ++ L9174 ++ [F219] = L9172 from rfl, show [F51] ++ L9174 = L9168 from rfl,
    show L9174 ++ [F219] = L9170 from rfl] at h
  rw [i5421 hinj, i5419 hinj, i5420 hinj, i5422 hinj] at h
  linarith

theorem row1902 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9175 + (1 : ℝ) * HLm Γ 5 L9177 + (-1 : ℝ) * HLm Γ 5 L9179 + (-1 : ℝ) * HLm Γ 5 L9181 := by
  have h := HLm_submod hΓ [F7] L9182 [F86]
  rw [show [F7] ++ L9182 ++ [F86] = L9180 from rfl, show [F7] ++ L9182 = L9176 from rfl,
    show L9182 ++ [F86] = L9178 from rfl] at h
  rw [i5425 hinj, i5423 hinj, i5424 hinj, i5426 hinj] at h
  linarith

theorem row1903 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9183 + (1 : ℝ) * HLm Γ 5 L9185 + (-1 : ℝ) * HLm Γ 5 L9187 + (-1 : ℝ) * HLm Γ 5 L9189 := by
  have h := HLm_submod hΓ [F228] L9190 [F85]
  rw [show [F228] ++ L9190 ++ [F85] = L9188 from rfl, show [F228] ++ L9190 = L9184 from rfl,
    show L9190 ++ [F85] = L9186 from rfl] at h
  rw [i5429 hinj, i5427 hinj, i5428 hinj, i5430 hinj] at h
  linarith

theorem row1904 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5095 + (1 : ℝ) * HLm Γ 5 L9192 + (-1 : ℝ) * HLm Γ 5 L9194 + (-1 : ℝ) * HLm Γ 5 L3761 := by
  have h := HLm_submod hΓ [F210] L3762 [F43]
  rw [show [F210] ++ L3762 ++ [F43] = L9195 from rfl, show [F210] ++ L3762 = L9191 from rfl,
    show L3762 ++ [F43] = L9193 from rfl] at h
  rw [i5433 hinj, i5431 hinj, i5432 hinj, i2102 hinj] at h
  linarith

theorem row1905 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9196 + (1 : ℝ) * HLm Γ 5 L9198 + (-1 : ℝ) * HLm Γ 5 L9200 + (-1 : ℝ) * HLm Γ 5 L8096 := by
  have h := HLm_submod hΓ [F51] L8097 [F210]
  rw [show [F51] ++ L8097 ++ [F210] = L9201 from rfl, show [F51] ++ L8097 = L9197 from rfl,
    show L8097 ++ [F210] = L9199 from rfl] at h
  rw [i5436 hinj, i5434 hinj, i5435 hinj, i4775 hinj] at h
  linarith

theorem row1906 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9202 + (1 : ℝ) * HLm Γ 5 L9204 + (-1 : ℝ) * HLm Γ 5 L9206 + (-1 : ℝ) * HLm Γ 5 L9208 := by
  have h := HLm_submod hΓ [F0] L9209 [F25]
  rw [show [F0] ++ L9209 ++ [F25] = L9207 from rfl, show [F0] ++ L9209 = L9203 from rfl,
    show L9209 ++ [F25] = L9205 from rfl] at h
  rw [i5439 hinj, i5437 hinj, i5438 hinj, i5440 hinj] at h
  linarith

theorem row1907 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9210 + (1 : ℝ) * HLm Γ 5 L7863 + (-1 : ℝ) * HLm Γ 5 L9212 + (-1 : ℝ) * HLm Γ 5 L7860 := by
  have h := HLm_submod hΓ [F7] L7861 [F210]
  rw [show [F7] ++ L7861 ++ [F210] = L9213 from rfl, show [F7] ++ L7861 = L9211 from rfl,
    show L7861 ++ [F210] = L7864 from rfl] at h
  rw [i5442 hinj, i5441 hinj, i4641 hinj, i4639 hinj] at h
  linarith

theorem row1908 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9214 + (1 : ℝ) * HLm Γ 5 L9216 + (-1 : ℝ) * HLm Γ 5 L9218 + (-1 : ℝ) * HLm Γ 5 L9220 := by
  have h := HLm_submod hΓ [F210] L9221 [F33]
  rw [show [F210] ++ L9221 ++ [F33] = L9219 from rfl, show [F210] ++ L9221 = L9215 from rfl,
    show L9221 ++ [F33] = L9217 from rfl] at h
  rw [i5445 hinj, i5443 hinj, i5444 hinj, i5446 hinj] at h
  linarith

theorem row1909 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9222 + (1 : ℝ) * HLm Γ 5 L9224 + (-1 : ℝ) * HLm Γ 5 L9226 + (-1 : ℝ) * HLm Γ 5 L2966 := by
  have h := HLm_submod hΓ [F210] L9228 [F90]
  rw [show [F210] ++ L9228 ++ [F90] = L9227 from rfl, show [F210] ++ L9228 = L9223 from rfl,
    show L9228 ++ [F90] = L9225 from rfl] at h
  rw [i5449 hinj, i5447 hinj, i5448 hinj, i5450 hinj] at h
  linarith

theorem row1910 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7653 + (1 : ℝ) * HLm Γ 5 L7712 + (-1 : ℝ) * HLm Γ 5 L9231 + (-1 : ℝ) * HLm Γ 5 L7020 := by
  have h := HLm_submod hΓ [F46] L9233 [F210]
  rw [show [F46] ++ L9233 ++ [F210] = L9232 from rfl, show [F46] ++ L9233 = L9229 from rfl,
    show L9233 ++ [F210] = L9230 from rfl] at h
  rw [i5453 hinj, i5451 hinj, i5452 hinj, i5454 hinj] at h
  linarith

theorem row1911 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L970 + (1 : ℝ) * HLm Γ 5 L2421 + (-1 : ℝ) * HLm Γ 5 L1694 + (-1 : ℝ) * HLm Γ 5 L7678 := by
  have h := HLm_submod hΓ [F0] L9237 [F2]
  rw [show [F0] ++ L9237 ++ [F2] = L9236 from rfl, show [F0] ++ L9237 = L9234 from rfl,
    show L9237 ++ [F2] = L9235 from rfl] at h
  rw [i5457 hinj, i5455 hinj, i5456 hinj, i5458 hinj] at h
  linarith

theorem row1912 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9202 + (1 : ℝ) * HLm Γ 5 L7682 + (-1 : ℝ) * HLm Γ 5 L9240 + (-1 : ℝ) * HLm Γ 5 L7680 := by
  have h := HLm_submod hΓ [F0] L7681 [F96]
  rw [show [F0] ++ L7681 ++ [F96] = L9241 from rfl, show [F0] ++ L7681 = L9238 from rfl,
    show L7681 ++ [F96] = L9239 from rfl] at h
  rw [i5461 hinj, i5459 hinj, i5460 hinj, i4543 hinj] at h
  linarith

theorem row1913 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9242 + (1 : ℝ) * HLm Γ 5 L9244 + (-1 : ℝ) * HLm Γ 5 L6434 + (-1 : ℝ) * HLm Γ 5 L9247 := by
  have h := HLm_submod hΓ [F0] L9248 [F3]
  rw [show [F0] ++ L9248 ++ [F3] = L9246 from rfl, show [F0] ++ L9248 = L9243 from rfl,
    show L9248 ++ [F3] = L9245 from rfl] at h
  rw [i5464 hinj, i5462 hinj, i5463 hinj, i5465 hinj] at h
  linarith

theorem row1914 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9249 + (1 : ℝ) * HLm Γ 5 L9251 + (-1 : ℝ) * HLm Γ 5 L9253 + (-1 : ℝ) * HLm Γ 5 L9255 := by
  have h := HLm_submod hΓ [F0] L9255 [F3]
  rw [show [F0] ++ L9255 ++ [F3] = L9254 from rfl, show [F0] ++ L9255 = L9250 from rfl,
    show L9255 ++ [F3] = L9252 from rfl] at h
  rw [i5468 hinj, i5466 hinj, i5467 hinj] at h
  linarith

theorem row1915 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9256 + (1 : ℝ) * HLm Γ 5 L7703 + (-1 : ℝ) * HLm Γ 5 L9259 + (-1 : ℝ) * HLm Γ 5 L7701 := by
  have h := HLm_submod hΓ [F7] L9261 [F6]
  rw [show [F7] ++ L9261 ++ [F6] = L9260 from rfl, show [F7] ++ L9261 = L9257 from rfl,
    show L9261 ++ [F6] = L9258 from rfl] at h
  rw [i5471 hinj, i5469 hinj, i5470 hinj, i5472 hinj] at h
  linarith

theorem row1916 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5739 + (1 : ℝ) * HLm Γ 5 L8389 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L9265 := by
  have h := HLm_submod hΓ [F10] L9266 [F4]
  rw [show [F10] ++ L9266 ++ [F4] = L9264 from rfl, show [F10] ++ L9266 = L9262 from rfl,
    show L9266 ++ [F4] = L9263 from rfl] at h
  rw [i5475 hinj, i5473 hinj, i5474 hinj, i5476 hinj] at h
  linarith

theorem row1917 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9267 + (1 : ℝ) * HLm Γ 5 L9269 + (-1 : ℝ) * HLm Γ 5 L9271 + (-1 : ℝ) * HLm Γ 5 L7697 := by
  have h := HLm_submod hΓ [F44] L7698 [F211]
  rw [show [F44] ++ L7698 ++ [F211] = L9272 from rfl, show [F44] ++ L7698 = L9268 from rfl,
    show L7698 ++ [F211] = L9270 from rfl] at h
  rw [i5479 hinj, i5477 hinj, i5478 hinj, i4552 hinj] at h
  linarith

theorem row1918 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9273 + (1 : ℝ) * HLm Γ 5 L7699 + (-1 : ℝ) * HLm Γ 5 L9276 + (-1 : ℝ) * HLm Γ 5 L7697 := by
  have h := HLm_submod hΓ [F46] L7698 [F210]
  rw [show [F46] ++ L7698 ++ [F210] = L9277 from rfl, show [F46] ++ L7698 = L9274 from rfl,
    show L7698 ++ [F210] = L9275 from rfl] at h
  rw [i5482 hinj, i5480 hinj, i5481 hinj, i4552 hinj] at h
  linarith

theorem row1919 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7274 + (1 : ℝ) * HLm Γ 5 L9279 + (-1 : ℝ) * HLm Γ 5 L9281 + (-1 : ℝ) * HLm Γ 5 L9283 := by
  have h := HLm_submod hΓ [F7] L9284 [F6]
  rw [show [F7] ++ L9284 ++ [F6] = L9282 from rfl, show [F7] ++ L9284 = L9278 from rfl,
    show L9284 ++ [F6] = L9280 from rfl] at h
  rw [i5485 hinj, i5483 hinj, i5484 hinj, i5486 hinj] at h
  linarith

theorem row1920 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9285 + (1 : ℝ) * HLm Γ 5 L9287 + (-1 : ℝ) * HLm Γ 5 L9289 + (-1 : ℝ) * HLm Γ 5 L9291 := by
  have h := HLm_submod hΓ [F62] L9292 [F214]
  rw [show [F62] ++ L9292 ++ [F214] = L9290 from rfl, show [F62] ++ L9292 = L9286 from rfl,
    show L9292 ++ [F214] = L9288 from rfl] at h
  rw [i5489 hinj, i5487 hinj, i5488 hinj, i5490 hinj] at h
  linarith

theorem row1921 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9293 + (1 : ℝ) * HLm Γ 5 L9295 + (-1 : ℝ) * HLm Γ 5 L9297 + (-1 : ℝ) * HLm Γ 5 L9299 := by
  have h := HLm_submod hΓ [F7] L9300 [F219]
  rw [show [F7] ++ L9300 ++ [F219] = L9298 from rfl, show [F7] ++ L9300 = L9294 from rfl,
    show L9300 ++ [F219] = L9296 from rfl] at h
  rw [i5493 hinj, i5491 hinj, i5492 hinj, i5494 hinj] at h
  linarith

theorem row1922 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4798 + (1 : ℝ) * HLm Γ 5 L9302 + (-1 : ℝ) * HLm Γ 5 L4801 + (-1 : ℝ) * HLm Γ 5 L3810 := by
  have h := HLm_submod hΓ [F1] L3811 [F67]
  rw [show [F1] ++ L3811 ++ [F67] = L9304 from rfl, show [F1] ++ L3811 = L9301 from rfl,
    show L3811 ++ [F67] = L9303 from rfl] at h
  rw [i5497 hinj, i5495 hinj, i5496 hinj, i2130 hinj] at h
  linarith

theorem row1923 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9305 + (1 : ℝ) * HLm Γ 5 L9307 + (-1 : ℝ) * HLm Γ 5 L9309 + (-1 : ℝ) * HLm Γ 5 L3836 := by
  have h := HLm_submod hΓ [F0] L9311 [F45]
  rw [show [F0] ++ L9311 ++ [F45] = L9310 from rfl, show [F0] ++ L9311 = L9306 from rfl,
    show L9311 ++ [F45] = L9308 from rfl] at h
  rw [i5500 hinj, i5498 hinj, i5499 hinj, i5501 hinj] at h
  linarith

theorem row1924 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5020 + (1 : ℝ) * HLm Γ 5 L9312 + (-1 : ℝ) * HLm Γ 5 L9314 + (-1 : ℝ) * HLm Γ 5 L9316 := by
  have h := HLm_submod hΓ [F3] L9317 [F210]
  rw [show [F3] ++ L9317 ++ [F210] = L9315 from rfl, show [F3] ++ L9317 = L6272 from rfl,
    show L9317 ++ [F210] = L9313 from rfl] at h
  rw [i5503 hinj, i3614 hinj, i5502 hinj, i5504 hinj] at h
  linarith

theorem row1925 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9318 + (1 : ℝ) * HLm Γ 5 L9320 + (-1 : ℝ) * HLm Γ 5 L6356 + (-1 : ℝ) * HLm Γ 5 L1091 := by
  have h := HLm_submod hΓ [F2] L5190 [F210]
  rw [show [F2] ++ L5190 ++ [F210] = L9322 from rfl, show [F2] ++ L5190 = L9319 from rfl,
    show L5190 ++ [F210] = L9321 from rfl] at h
  rw [i5507 hinj, i5505 hinj, i5506 hinj, i2923 hinj] at h
  linarith

theorem row1926 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5106 + (1 : ℝ) * HLm Γ 5 L9324 + (-1 : ℝ) * HLm Γ 5 L9326 + (-1 : ℝ) * HLm Γ 5 L9328 := by
  have h := HLm_submod hΓ [F2] L9329 [F17]
  rw [show [F2] ++ L9329 ++ [F17] = L9327 from rfl, show [F2] ++ L9329 = L9323 from rfl,
    show L9329 ++ [F17] = L9325 from rfl] at h
  rw [i5510 hinj, i5508 hinj, i5509 hinj, i5511 hinj] at h
  linarith

theorem row1927 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7559 + (1 : ℝ) * HLm Γ 5 L3696 + (-1 : ℝ) * HLm Γ 5 L9332 + (-1 : ℝ) * HLm Γ 5 L9334 := by
  have h := HLm_submod hΓ [F9] L9335 [F3]
  rw [show [F9] ++ L9335 ++ [F3] = L9333 from rfl, show [F9] ++ L9335 = L9330 from rfl,
    show L9335 ++ [F3] = L9331 from rfl] at h
  rw [i5514 hinj, i5512 hinj, i5513 hinj, i5515 hinj] at h
  linarith

theorem row1928 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9336 + (1 : ℝ) * HLm Γ 5 L9338 + (-1 : ℝ) * HLm Γ 5 L9326 + (-1 : ℝ) * HLm Γ 5 L7744 := by
  have h := HLm_submod hΓ [F2] L7745 [F210]
  rw [show [F2] ++ L7745 ++ [F210] = L9340 from rfl, show [F2] ++ L7745 = L9337 from rfl,
    show L7745 ++ [F210] = L9339 from rfl] at h
  rw [i5518 hinj, i5516 hinj, i5517 hinj, i4577 hinj] at h
  linarith

theorem row1929 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9336 + (1 : ℝ) * HLm Γ 5 L7746 + (-1 : ℝ) * HLm Γ 5 L9342 + (-1 : ℝ) * HLm Γ 5 L7744 := by
  have h := HLm_submod hΓ [F2] L7745 [F228]
  rw [show [F2] ++ L7745 ++ [F228] = L9343 from rfl, show [F2] ++ L7745 = L9337 from rfl,
    show L7745 ++ [F228] = L9341 from rfl] at h
  rw [i5520 hinj, i5516 hinj, i5519 hinj, i4577 hinj] at h
  linarith

theorem row1930 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9344 + (1 : ℝ) * HLm Γ 5 L9346 + (-1 : ℝ) * HLm Γ 5 L9348 + (-1 : ℝ) * HLm Γ 5 L7768 := by
  have h := HLm_submod hΓ [F7] L9350 [F85]
  rw [show [F7] ++ L9350 ++ [F85] = L9349 from rfl, show [F7] ++ L9350 = L9345 from rfl,
    show L9350 ++ [F85] = L9347 from rfl] at h
  rw [i5523 hinj, i5521 hinj, i5522 hinj, i5524 hinj] at h
  linarith

theorem row1931 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9351 + (1 : ℝ) * HLm Γ 5 L7774 + (-1 : ℝ) * HLm Γ 5 L9354 + (-1 : ℝ) * HLm Γ 5 L7772 := by
  have h := HLm_submod hΓ [F46] L9356 [F85]
  rw [show [F46] ++ L9356 ++ [F85] = L9355 from rfl, show [F46] ++ L9356 = L9352 from rfl,
    show L9356 ++ [F85] = L9353 from rfl] at h
  rw [i5527 hinj, i5525 hinj, i5526 hinj, i5528 hinj] at h
  linarith

theorem row1932 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9357 + (1 : ℝ) * HLm Γ 5 L7766 + (-1 : ℝ) * HLm Γ 5 L9360 + (-1 : ℝ) * HLm Γ 5 L8012 := by
  have h := HLm_submod hΓ [F51] L8013 [F210]
  rw [show [F51] ++ L8013 ++ [F210] = L9361 from rfl, show [F51] ++ L8013 = L9358 from rfl,
    show L8013 ++ [F210] = L9359 from rfl] at h
  rw [i5531 hinj, i5529 hinj, i5530 hinj, i4723 hinj] at h
  linarith

theorem row1933 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9362 + (1 : ℝ) * HLm Γ 5 L4974 + (-1 : ℝ) * HLm Γ 5 L4448 + (-1 : ℝ) * HLm Γ 5 L9366 := by
  have h := HLm_submod hΓ [F7] L9367 [F12]
  rw [show [F7] ++ L9367 ++ [F12] = L9365 from rfl, show [F7] ++ L9367 = L9363 from rfl,
    show L9367 ++ [F12] = L9364 from rfl] at h
  rw [i5534 hinj, i5532 hinj, i5533 hinj, i5535 hinj] at h
  linarith

theorem row1934 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9202 + (1 : ℝ) * HLm Γ 5 L7825 + (-1 : ℝ) * HLm Γ 5 L9370 + (-1 : ℝ) * HLm Γ 5 L7822 := by
  have h := HLm_submod hΓ [F0] L9372 [F36]
  rw [show [F0] ++ L9372 ++ [F36] = L9371 from rfl, show [F0] ++ L9372 = L9368 from rfl,
    show L9372 ++ [F36] = L9369 from rfl] at h
  rw [i5538 hinj, i5536 hinj, i5537 hinj, i5539 hinj] at h
  linarith

theorem row1935 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3883 + (1 : ℝ) * HLm Γ 5 L9373 + (-1 : ℝ) * HLm Γ 5 L9375 + (-1 : ℝ) * HLm Γ 5 L3933 := by
  have h := HLm_submod hΓ [F0] L5251 [F3]
  rw [show [F0] ++ L5251 ++ [F3] = L9376 from rfl, show [F0] ++ L5251 = L5247 from rfl,
    show L5251 ++ [F3] = L9374 from rfl] at h
  rw [i5541 hinj, i2958 hinj, i5540 hinj, i2961 hinj] at h
  linarith

theorem row1936 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9377 + (1 : ℝ) * HLm Γ 5 L9379 + (-1 : ℝ) * HLm Γ 5 L9381 + (-1 : ℝ) * HLm Γ 5 L9383 := by
  have h := HLm_submod hΓ [F3] L9384 [F85]
  rw [show [F3] ++ L9384 ++ [F85] = L9382 from rfl, show [F3] ++ L9384 = L9378 from rfl,
    show L9384 ++ [F85] = L9380 from rfl] at h
  rw [i5544 hinj, i5542 hinj, i5543 hinj, i5545 hinj] at h
  linarith

theorem row1937 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9385 + (1 : ℝ) * HLm Γ 5 L9387 + (-1 : ℝ) * HLm Γ 5 L9389 + (-1 : ℝ) * HLm Γ 5 L7797 := by
  have h := HLm_submod hΓ [F2] L7798 [F9]
  rw [show [F2] ++ L7798 ++ [F9] = L9390 from rfl, show [F2] ++ L7798 = L9386 from rfl,
    show L7798 ++ [F9] = L9388 from rfl] at h
  rw [i5548 hinj, i5546 hinj, i5547 hinj, i4607 hinj] at h
  linarith

theorem row1938 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9391 + (1 : ℝ) * HLm Γ 5 L7805 + (-1 : ℝ) * HLm Γ 5 L9394 + (-1 : ℝ) * HLm Γ 5 L7803 := by
  have h := HLm_submod hΓ [F16] L7804 [F210]
  rw [show [F16] ++ L7804 ++ [F210] = L9395 from rfl, show [F16] ++ L7804 = L9392 from rfl,
    show L7804 ++ [F210] = L9393 from rfl] at h
  rw [i5551 hinj, i5549 hinj, i5550 hinj, i4610 hinj] at h
  linarith

theorem row1939 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9396 + (1 : ℝ) * HLm Γ 5 L9398 + (-1 : ℝ) * HLm Γ 5 L9400 + (-1 : ℝ) * HLm Γ 5 L9402 := by
  have h := HLm_submod hΓ [F211] L9403 [F90]
  rw [show [F211] ++ L9403 ++ [F90] = L9401 from rfl, show [F211] ++ L9403 = L9397 from rfl,
    show L9403 ++ [F90] = L9399 from rfl] at h
  rw [i5554 hinj, i5552 hinj, i5553 hinj, i5555 hinj] at h
  linarith

theorem row1940 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9404 + (1 : ℝ) * HLm Γ 5 L9406 + (-1 : ℝ) * HLm Γ 5 L9408 + (-1 : ℝ) * HLm Γ 5 L9410 := by
  have h := HLm_submod hΓ [F210] L9411 [F34]
  rw [show [F210] ++ L9411 ++ [F34] = L9409 from rfl, show [F210] ++ L9411 = L9405 from rfl,
    show L9411 ++ [F34] = L9407 from rfl] at h
  rw [i5558 hinj, i5556 hinj, i5557 hinj, i5559 hinj] at h
  linarith

theorem row1941 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9412 + (1 : ℝ) * HLm Γ 5 L9414 + (-1 : ℝ) * HLm Γ 5 L9416 + (-1 : ℝ) * HLm Γ 5 L7842 := by
  have h := HLm_submod hΓ [F3] L9418 [F85]
  rw [show [F3] ++ L9418 ++ [F85] = L9417 from rfl, show [F3] ++ L9418 = L9413 from rfl,
    show L9418 ++ [F85] = L9415 from rfl] at h
  rw [i5562 hinj, i5560 hinj, i5561 hinj, i5563 hinj] at h
  linarith

theorem row1942 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9419 + (1 : ℝ) * HLm Γ 5 L5262 + (-1 : ℝ) * HLm Γ 5 L9422 + (-1 : ℝ) * HLm Γ 5 L3941 := by
  have h := HLm_submod hΓ [F7] L3942 [F2]
  rw [show [F7] ++ L3942 ++ [F2] = L9423 from rfl, show [F7] ++ L3942 = L9420 from rfl,
    show L3942 ++ [F2] = L9421 from rfl] at h
  rw [i5566 hinj, i5564 hinj, i5565 hinj, i2200 hinj] at h
  linarith

theorem row1943 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9424 + (1 : ℝ) * HLm Γ 5 L9426 + (-1 : ℝ) * HLm Γ 5 L9428 + (-1 : ℝ) * HLm Γ 5 L9430 := by
  have h := HLm_submod hΓ [F111] L9431 [F210]
  rw [show [F111] ++ L9431 ++ [F210] = L9429 from rfl, show [F111] ++ L9431 = L9425 from rfl,
    show L9431 ++ [F210] = L9427 from rfl] at h
  rw [i5569 hinj, i5567 hinj, i5568 hinj, i5570 hinj] at h
  linarith

theorem row1944 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9432 + (1 : ℝ) * HLm Γ 5 L7873 + (-1 : ℝ) * HLm Γ 5 L9435 + (-1 : ℝ) * HLm Γ 5 L7871 := by
  have h := HLm_submod hΓ [F51] L9437 [F214]
  rw [show [F51] ++ L9437 ++ [F214] = L9436 from rfl, show [F51] ++ L9437 = L9433 from rfl,
    show L9437 ++ [F214] = L9434 from rfl] at h
  rw [i5573 hinj, i5571 hinj, i5572 hinj, i5574 hinj] at h
  linarith

theorem row1945 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9438 + (1 : ℝ) * HLm Γ 5 L9440 + (-1 : ℝ) * HLm Γ 5 L9442 + (-1 : ℝ) * HLm Γ 5 L7128 := by
  have h := HLm_submod hΓ [F2] L9444 [F236]
  rw [show [F2] ++ L9444 ++ [F236] = L9443 from rfl, show [F2] ++ L9444 = L9439 from rfl,
    show L9444 ++ [F236] = L9441 from rfl] at h
  rw [i5577 hinj, i5575 hinj, i5576 hinj, i5578 hinj] at h
  linarith

theorem row1946 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8081 + (1 : ℝ) * HLm Γ 5 L7867 + (-1 : ℝ) * HLm Γ 5 L4469 + (-1 : ℝ) * HLm Γ 5 L8079 := by
  have h := HLm_submod hΓ [F7] L9448 [F210]
  rw [show [F7] ++ L9448 ++ [F210] = L9447 from rfl, show [F7] ++ L9448 = L9445 from rfl,
    show L9448 ++ [F210] = L9446 from rfl] at h
  rw [i5581 hinj, i5579 hinj, i5580 hinj, i5582 hinj] at h
  linarith

theorem row1947 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9449 + (1 : ℝ) * HLm Γ 5 L9451 + (-1 : ℝ) * HLm Γ 5 L9453 + (-1 : ℝ) * HLm Γ 5 L9455 := by
  have h := HLm_submod hΓ [F22] L9456 [F210]
  rw [show [F22] ++ L9456 ++ [F210] = L9454 from rfl, show [F22] ++ L9456 = L9450 from rfl,
    show L9456 ++ [F210] = L9452 from rfl] at h
  rw [i5585 hinj, i5583 hinj, i5584 hinj, i5586 hinj] at h
  linarith

theorem row1948 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7439 + (1 : ℝ) * HLm Γ 5 L9458 + (-1 : ℝ) * HLm Γ 5 L9460 + (-1 : ℝ) * HLm Γ 5 L7894 := by
  have h := HLm_submod hΓ [F7] L9462 [F211]
  rw [show [F7] ++ L9462 ++ [F211] = L9461 from rfl, show [F7] ++ L9462 = L9457 from rfl,
    show L9462 ++ [F211] = L9459 from rfl] at h
  rw [i5589 hinj, i5587 hinj, i5588 hinj, i5590 hinj] at h
  linarith

theorem row1949 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9463 + (1 : ℝ) * HLm Γ 5 L9465 + (-1 : ℝ) * HLm Γ 5 L9467 + (-1 : ℝ) * HLm Γ 5 L9469 := by
  have h := HLm_submod hΓ [F214] L9470 [F27]
  rw [show [F214] ++ L9470 ++ [F27] = L9468 from rfl, show [F214] ++ L9470 = L9464 from rfl,
    show L9470 ++ [F27] = L9466 from rfl] at h
  rw [i5593 hinj, i5591 hinj, i5592 hinj, i5594 hinj] at h
  linarith

end EntropyBounds.TwoSet.Certs.R7A5
