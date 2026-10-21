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

theorem row1350 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L6012 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6010 := by
  have h := HLm_submod hΓ [F0] L6690 [F210]
  rw [show [F0] ++ L6690 ++ [F210] = L6689 from rfl, show [F0] ++ L6690 = L6687 from rfl,
    show L6690 ++ [F210] = L6688 from rfl] at h
  rw [i3955 hinj, i3953 hinj, i3954 hinj, i3956 hinj] at h
  linarith

theorem row1351 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L6025 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6023 := by
  have h := HLm_submod hΓ [F0] L6024 [F210]
  rw [show [F0] ++ L6024 ++ [F210] = L6693 from rfl, show [F0] ++ L6024 = L6691 from rfl,
    show L6024 ++ [F210] = L6692 from rfl] at h
  rw [i3959 hinj, i3957 hinj, i3958 hinj, i3441 hinj] at h
  linarith

theorem row1352 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6694 + (1 : ℝ) * HLm Γ 5 L6031 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6029 := by
  have h := HLm_submod hΓ [F0] L6698 [F9]
  rw [show [F0] ++ L6698 ++ [F9] = L6697 from rfl, show [F0] ++ L6698 = L6695 from rfl,
    show L6698 ++ [F9] = L6696 from rfl] at h
  rw [i3962 hinj, i3960 hinj, i3961 hinj, i3963 hinj] at h
  linarith

theorem row1353 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L6315 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6312 := by
  have h := HLm_submod hΓ [F0] L6702 [F210]
  rw [show [F0] ++ L6702 ++ [F210] = L6701 from rfl, show [F0] ++ L6702 = L6699 from rfl,
    show L6702 ++ [F210] = L6700 from rfl] at h
  rw [i3966 hinj, i3964 hinj, i3965 hinj, i3967 hinj] at h
  linarith

theorem row1354 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L6108 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6104 := by
  have h := HLm_submod hΓ [F0] L6706 [F210]
  rw [show [F0] ++ L6706 ++ [F210] = L6705 from rfl, show [F0] ++ L6706 = L6703 from rfl,
    show L6706 ++ [F210] = L6704 from rfl] at h
  rw [i3970 hinj, i3968 hinj, i3969 hinj, i3971 hinj] at h
  linarith

theorem row1355 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L6708 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6711 := by
  have h := HLm_submod hΓ [F0] L6712 [F210]
  rw [show [F0] ++ L6712 ++ [F210] = L6710 from rfl, show [F0] ++ L6712 = L6707 from rfl,
    show L6712 ++ [F210] = L6709 from rfl] at h
  rw [i3974 hinj, i3972 hinj, i3973 hinj, i3975 hinj] at h
  linarith

theorem row1356 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L6127 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6124 := by
  have h := HLm_submod hΓ [F0] L6716 [F210]
  rw [show [F0] ++ L6716 ++ [F210] = L6715 from rfl, show [F0] ++ L6716 = L6713 from rfl,
    show L6716 ++ [F210] = L6714 from rfl] at h
  rw [i3978 hinj, i3976 hinj, i3977 hinj, i3979 hinj] at h
  linarith

theorem row1357 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6089 + (1 : ℝ) * HLm Γ 5 L6718 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6721 := by
  have h := HLm_submod hΓ [F1] L6722 [F0]
  rw [show [F1] ++ L6722 ++ [F0] = L6720 from rfl, show [F1] ++ L6722 = L6717 from rfl,
    show L6722 ++ [F0] = L6719 from rfl] at h
  rw [i3982 hinj, i3980 hinj, i3981 hinj, i3983 hinj] at h
  linarith

theorem row1358 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6174 + (1 : ℝ) * HLm Γ 5 L6141 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6139 := by
  have h := HLm_submod hΓ [F1] L6140 [F2]
  rw [show [F1] ++ L6140 ++ [F2] = L6725 from rfl, show [F1] ++ L6140 = L6723 from rfl,
    show L6140 ++ [F2] = L6724 from rfl] at h
  rw [i3986 hinj, i3984 hinj, i3985 hinj, i3522 hinj] at h
  linarith

theorem row1359 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4787 + (1 : ℝ) * HLm Γ 5 L5524 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L4871 := by
  have h := HLm_submod hΓ [F1] L6146 [F0]
  rw [show [F1] ++ L6146 ++ [F0] = L6728 from rfl, show [F1] ++ L6146 = L6726 from rfl,
    show L6146 ++ [F0] = L6727 from rfl] at h
  rw [i3989 hinj, i3987 hinj, i3988 hinj, i3526 hinj] at h
  linarith

theorem row1360 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6157 + (1 : ℝ) * HLm Γ 5 L6729 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6155 := by
  have h := HLm_submod hΓ [F1] L6156 [F2]
  rw [show [F1] ++ L6156 ++ [F2] = L6731 from rfl, show [F1] ++ L6156 = L6158 from rfl,
    show L6156 ++ [F2] = L6730 from rfl] at h
  rw [i3991 hinj, i3535 hinj, i3990 hinj, i3534 hinj] at h
  linarith

theorem row1361 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L6163 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6161 := by
  have h := HLm_submod hΓ [F0] L6735 [F210]
  rw [show [F0] ++ L6735 ++ [F210] = L6734 from rfl, show [F0] ++ L6735 = L6732 from rfl,
    show L6735 ++ [F210] = L6733 from rfl] at h
  rw [i3994 hinj, i3992 hinj, i3993 hinj, i3995 hinj] at h
  linarith

theorem row1362 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L6209 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6207 := by
  have h := HLm_submod hΓ [F0] L6208 [F210]
  rw [show [F0] ++ L6208 ++ [F210] = L6738 from rfl, show [F0] ++ L6208 = L6736 from rfl,
    show L6208 ++ [F210] = L6737 from rfl] at h
  rw [i3998 hinj, i3996 hinj, i3997 hinj, i3569 hinj] at h
  linarith

theorem row1363 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L6375 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6371 := by
  have h := HLm_submod hΓ [F0] L6742 [F210]
  rw [show [F0] ++ L6742 ++ [F210] = L6741 from rfl, show [F0] ++ L6742 = L6739 from rfl,
    show L6742 ++ [F210] = L6740 from rfl] at h
  rw [i4001 hinj, i3999 hinj, i4000 hinj, i4002 hinj] at h
  linarith

theorem row1364 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L6238 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6235 := by
  have h := HLm_submod hΓ [F0] L6746 [F210]
  rw [show [F0] ++ L6746 ++ [F210] = L6745 from rfl, show [F0] ++ L6746 = L6743 from rfl,
    show L6746 ++ [F210] = L6744 from rfl] at h
  rw [i4005 hinj, i4003 hinj, i4004 hinj, i4006 hinj] at h
  linarith

theorem row1365 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L6233 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6231 := by
  have h := HLm_submod hΓ [F0] L6750 [F210]
  rw [show [F0] ++ L6750 ++ [F210] = L6749 from rfl, show [F0] ++ L6750 = L6747 from rfl,
    show L6750 ++ [F210] = L6748 from rfl] at h
  rw [i4009 hinj, i4007 hinj, i4008 hinj, i4010 hinj] at h
  linarith

theorem row1366 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4558 + (1 : ℝ) * HLm Γ 5 L6244 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6242 := by
  have h := HLm_submod hΓ [F0] L6754 [F67]
  rw [show [F0] ++ L6754 ++ [F67] = L6753 from rfl, show [F0] ++ L6754 = L6751 from rfl,
    show L6754 ++ [F67] = L6752 from rfl] at h
  rw [i4013 hinj, i4011 hinj, i4012 hinj, i4014 hinj] at h
  linarith

theorem row1367 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6270 + (1 : ℝ) * HLm Γ 5 L2833 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6262 := by
  have h := HLm_submod hΓ [F0] L6263 [F51]
  rw [show [F0] ++ L6263 ++ [F51] = L6757 from rfl, show [F0] ++ L6263 = L6755 from rfl,
    show L6263 ++ [F51] = L6756 from rfl] at h
  rw [i4017 hinj, i4015 hinj, i4016 hinj, i3608 hinj] at h
  linarith

theorem row1368 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L6285 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6283 := by
  have h := HLm_submod hΓ [F0] L6284 [F210]
  rw [show [F0] ++ L6284 ++ [F210] = L6760 from rfl, show [F0] ++ L6284 = L6758 from rfl,
    show L6284 ++ [F210] = L6759 from rfl] at h
  rw [i4020 hinj, i4018 hinj, i4019 hinj, i3624 hinj] at h
  linarith

theorem row1369 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L6290 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6288 := by
  have h := HLm_submod hΓ [F0] L6764 [F210]
  rw [show [F0] ++ L6764 ++ [F210] = L6763 from rfl, show [F0] ++ L6764 = L6761 from rfl,
    show L6764 ++ [F210] = L6762 from rfl] at h
  rw [i4023 hinj, i4021 hinj, i4022 hinj, i4024 hinj] at h
  linarith

theorem row1370 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L6294 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6292 := by
  have h := HLm_submod hΓ [F0] L6768 [F210]
  rw [show [F0] ++ L6768 ++ [F210] = L6767 from rfl, show [F0] ++ L6768 = L6765 from rfl,
    show L6768 ++ [F210] = L6766 from rfl] at h
  rw [i4027 hinj, i4025 hinj, i4026 hinj, i4028 hinj] at h
  linarith

theorem row1371 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L6347 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6344 := by
  have h := HLm_submod hΓ [F0] L6772 [F210]
  rw [show [F0] ++ L6772 ++ [F210] = L6771 from rfl, show [F0] ++ L6772 = L6769 from rfl,
    show L6772 ++ [F210] = L6770 from rfl] at h
  rw [i4031 hinj, i4029 hinj, i4030 hinj, i4032 hinj] at h
  linarith

theorem row1372 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L6338 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6335 := by
  have h := HLm_submod hΓ [F0] L6776 [F210]
  rw [show [F0] ++ L6776 ++ [F210] = L6775 from rfl, show [F0] ++ L6776 = L6773 from rfl,
    show L6776 ++ [F210] = L6774 from rfl] at h
  rw [i4035 hinj, i4033 hinj, i4034 hinj, i4036 hinj] at h
  linarith

theorem row1373 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L6333 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6331 := by
  have h := HLm_submod hΓ [F0] L6780 [F210]
  rw [show [F0] ++ L6780 ++ [F210] = L6779 from rfl, show [F0] ++ L6780 = L6777 from rfl,
    show L6780 ++ [F210] = L6778 from rfl] at h
  rw [i4039 hinj, i4037 hinj, i4038 hinj, i4040 hinj] at h
  linarith

theorem row1374 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6782 := by
  have h := HLm_mono Γ L6783 [F0]
  rw [show L6783 ++ [F0] = L6781 from rfl] at h
  rw [i4041 hinj, i4042 hinj] at h
  linarith

theorem row1375 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6785 := by
  have h := HLm_mono Γ L6786 [F0]
  rw [show L6786 ++ [F0] = L6784 from rfl] at h
  rw [i4043 hinj, i4044 hinj] at h
  linarith

theorem row1376 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6788 := by
  have h := HLm_mono Γ L6789 [F0]
  rw [show L6789 ++ [F0] = L6787 from rfl] at h
  rw [i4045 hinj, i4046 hinj] at h
  linarith

theorem row1377 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L15 + (1 : ℝ) * HLm Γ 5 L2836 + (-1 : ℝ) * HLm Γ 5 L6790 := by
  have h := HLm_submod hΓ [F7] ([] : List (Form 5)) [F217]
  rw [show [F7] ++ ([] : List (Form 5)) ++ [F217] = L6790 from rfl, show [F7] ++ ([] : List (Form 5)) = L15 from rfl,
    show ([] : List (Form 5)) ++ [F217] = L2836 from rfl] at h
  rw [HLm_nil (m := 5) hΓ] at h
  linarith

theorem row1378 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L136 + (1 : ℝ) * HLm Γ 5 L456 + (-1 : ℝ) * HLm Γ 5 L133 := by
  have h := HLm_submod hΓ [F51] ([] : List (Form 5)) [F45]
  rw [show [F51] ++ ([] : List (Form 5)) ++ [F45] = L133 from rfl, show [F51] ++ ([] : List (Form 5)) = L136 from rfl,
    show ([] : List (Form 5)) ++ [F45] = L456 from rfl] at h
  rw [HLm_nil (m := 5) hΓ] at h
  linarith

theorem row1379 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L26 + (1 : ℝ) * HLm Γ 5 L6791 + (-1 : ℝ) * HLm Γ 5 L2899 := by
  have h := HLm_submod hΓ [F10] ([] : List (Form 5)) [F219]
  rw [show [F10] ++ ([] : List (Form 5)) ++ [F219] = L6792 from rfl, show [F10] ++ ([] : List (Form 5)) = L27 from rfl,
    show ([] : List (Form 5)) ++ [F219] = L6791 from rfl] at h
  rw [i4047 hinj, i5 hinj, HLm_nil (m := 5) hΓ] at h
  linarith

theorem row1380 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7 + (1 : ℝ) * HLm Γ 5 L63 + (-1 : ℝ) * HLm Γ 5 L2875 := by
  have h := HLm_submod hΓ [F4] ([] : List (Form 5)) [F27]
  rw [show [F4] ++ ([] : List (Form 5)) ++ [F27] = L6793 from rfl, show [F4] ++ ([] : List (Form 5)) = L8 from rfl,
    show ([] : List (Form 5)) ++ [F27] = L63 from rfl] at h
  rw [i4048 hinj, i0 hinj, HLm_nil (m := 5) hΓ] at h
  linarith

theorem row1381 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L204 + (1 : ℝ) * HLm Γ 5 L6791 + (-1 : ℝ) * HLm Γ 5 L6794 := by
  have h := HLm_submod hΓ [F46] ([] : List (Form 5)) [F219]
  rw [show [F46] ++ ([] : List (Form 5)) ++ [F219] = L6794 from rfl, show [F46] ++ ([] : List (Form 5)) = L204 from rfl,
    show ([] : List (Form 5)) ++ [F219] = L6791 from rfl] at h
  rw [HLm_nil (m := 5) hΓ] at h
  linarith

theorem row1382 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2848 + (1 : ℝ) * HLm Γ 5 L76 + (-1 : ℝ) * HLm Γ 5 L6795 := by
  have h := HLm_submod hΓ [F67] ([] : List (Form 5)) [F36]
  rw [show [F67] ++ ([] : List (Form 5)) ++ [F36] = L6796 from rfl, show [F67] ++ ([] : List (Form 5)) = L2848 from rfl,
    show ([] : List (Form 5)) ++ [F36] = L76 from rfl] at h
  rw [i4049 hinj, HLm_nil (m := 5) hΓ] at h
  linarith

theorem row1383 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2850 + (1 : ℝ) * HLm Γ 5 L420 + (-1 : ℝ) * HLm Γ 5 L6797 := by
  have h := HLm_submod hΓ [F68] ([] : List (Form 5)) [F96]
  rw [show [F68] ++ ([] : List (Form 5)) ++ [F96] = L6798 from rfl, show [F68] ++ ([] : List (Form 5)) = L2850 from rfl,
    show ([] : List (Form 5)) ++ [F96] = L420 from rfl] at h
  rw [i4050 hinj, HLm_nil (m := 5) hΓ] at h
  linarith

theorem row1384 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L76 + (1 : ℝ) * HLm Γ 5 L456 + (-1 : ℝ) * HLm Γ 5 L6799 := by
  have h := HLm_submod hΓ [F36] ([] : List (Form 5)) [F45]
  rw [show [F36] ++ ([] : List (Form 5)) ++ [F45] = L6800 from rfl, show [F36] ++ ([] : List (Form 5)) = L76 from rfl,
    show ([] : List (Form 5)) ++ [F45] = L456 from rfl] at h
  rw [i4051 hinj, HLm_nil (m := 5) hΓ] at h
  linarith

theorem row1385 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4 + (1 : ℝ) * HLm Γ 5 L6802 + (-1 : ℝ) * HLm Γ 5 L2919 + (-1 : ℝ) * HLm Γ 5 L0 := by
  have h := HLm_submod hΓ [F2] L0 [F217]
  rw [show [F2] ++ L0 ++ [F217] = L6803 from rfl, show [F2] ++ L0 = L6801 from rfl,
    show L0 ++ [F217] = L6802 from rfl] at h
  rw [i4053 hinj, i4052 hinj] at h
  linarith

theorem row1386 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6804 + (1 : ℝ) * HLm Γ 5 L14 + (-1 : ℝ) * HLm Γ 5 L4045 + (-1 : ℝ) * HLm Γ 5 L0 := by
  have h := HLm_submod hΓ [F210] L0 [F6]
  rw [show [F210] ++ L0 ++ [F6] = L6806 from rfl, show [F210] ++ L0 = L6805 from rfl,
    show L0 ++ [F6] = L14 from rfl] at h
  rw [i4055 hinj, i4054 hinj] at h
  linarith

theorem row1387 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6807 + (1 : ℝ) * HLm Γ 5 L14 + (-1 : ℝ) * HLm Γ 5 L4065 + (-1 : ℝ) * HLm Γ 5 L0 := by
  have h := HLm_submod hΓ [F228] L0 [F6]
  rw [show [F228] ++ L0 ++ [F6] = L6809 from rfl, show [F228] ++ L0 = L6808 from rfl,
    show L0 ++ [F6] = L14 from rfl] at h
  rw [i4057 hinj, i4056 hinj] at h
  linarith

theorem row1388 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L108 + (1 : ℝ) * HLm Γ 5 L3303 + (-1 : ℝ) * HLm Γ 5 L3298 + (-1 : ℝ) * HLm Γ 5 L1 := by
  have h := HLm_submod hΓ [F7] L1 [F6]
  rw [show [F7] ++ L1 ++ [F6] = L3298 from rfl, show [F7] ++ L1 = L108 from rfl,
    show L1 ++ [F6] = L3303 from rfl] at h
  linarith

theorem row1389 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L26 + (1 : ℝ) * HLm Γ 5 L6810 + (-1 : ℝ) * HLm Γ 5 L74 + (-1 : ℝ) * HLm Γ 5 L15 := by
  have h := HLm_submod hΓ [F0] L15 [F34]
  rw [show [F0] ++ L15 ++ [F34] = L6812 from rfl, show [F0] ++ L15 = L26 from rfl,
    show L15 ++ [F34] = L6811 from rfl] at h
  rw [i4059 hinj, i4058 hinj] at h
  linarith

theorem row1390 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L16 + (1 : ℝ) * HLm Γ 5 L3159 + (-1 : ℝ) * HLm Γ 5 L4381 + (-1 : ℝ) * HLm Γ 5 L3 := by
  have h := HLm_submod hΓ [F7] L3 [F43]
  rw [show [F7] ++ L3 ++ [F43] = L4382 from rfl, show [F7] ++ L3 = L16 from rfl,
    show L3 ++ [F43] = L3164 from rfl] at h
  rw [i2456 hinj, i1790 hinj] at h
  linarith

theorem row1391 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6813 + (1 : ℝ) * HLm Γ 5 L6815 + (-1 : ℝ) * HLm Γ 5 L6817 + (-1 : ℝ) * HLm Γ 5 L3 := by
  have h := HLm_submod hΓ [F10] L3 [F219]
  rw [show [F10] ++ L3 ++ [F219] = L6818 from rfl, show [F10] ++ L3 = L6814 from rfl,
    show L3 ++ [F219] = L6816 from rfl] at h
  rw [i4062 hinj, i4060 hinj, i4061 hinj] at h
  linarith

theorem row1392 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2 + (1 : ℝ) * HLm Γ 5 L133 + (-1 : ℝ) * HLm Γ 5 L6819 + (-1 : ℝ) * HLm Γ 5 L136 := by
  have h := HLm_submod hΓ [F0] L136 [F45]
  rw [show [F0] ++ L136 ++ [F45] = L6820 from rfl, show [F0] ++ L136 = L1997 from rfl,
    show L136 ++ [F45] = L133 from rfl] at h
  rw [i4063 hinj, i1095 hinj] at h
  linarith

theorem row1393 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L131 + (1 : ℝ) * HLm Γ 5 L6821 + (-1 : ℝ) * HLm Γ 5 L6822 + (-1 : ℝ) * HLm Γ 5 L136 := by
  have h := HLm_submod hΓ [F46] L136 [F217]
  rw [show [F46] ++ L136 ++ [F217] = L6823 from rfl, show [F46] ++ L136 = L132 from rfl,
    show L136 ++ [F217] = L6821 from rfl] at h
  rw [i4064 hinj, i39 hinj] at h
  linarith

theorem row1394 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L137 + (1 : ℝ) * HLm Γ 5 L2883 + (-1 : ℝ) * HLm Γ 5 L6824 + (-1 : ℝ) * HLm Γ 5 L136 := by
  have h := HLm_submod hΓ [F16] L136 [F25]
  rw [show [F16] ++ L136 ++ [F25] = L6825 from rfl, show [F16] ++ L136 = L138 from rfl,
    show L136 ++ [F25] = L2883 from rfl] at h
  rw [i4065 hinj, i41 hinj] at h
  linarith

theorem row1395 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6826 + (1 : ℝ) * HLm Γ 5 L2003 + (-1 : ℝ) * HLm Γ 5 L6828 + (-1 : ℝ) * HLm Γ 5 L136 := by
  have h := HLm_submod hΓ [F236] L136 [F6]
  rw [show [F236] ++ L136 ++ [F6] = L6829 from rfl, show [F236] ++ L136 = L6827 from rfl,
    show L136 ++ [F6] = L2003 from rfl] at h
  rw [i4067 hinj, i4066 hinj] at h
  linarith

theorem row1396 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6830 + (1 : ℝ) * HLm Γ 5 L6821 + (-1 : ℝ) * HLm Γ 5 L6832 + (-1 : ℝ) * HLm Γ 5 L136 := by
  have h := HLm_submod hΓ [F17] L136 [F217]
  rw [show [F17] ++ L136 ++ [F217] = L6833 from rfl, show [F17] ++ L136 = L6831 from rfl,
    show L136 ++ [F217] = L6821 from rfl] at h
  rw [i4069 hinj, i4068 hinj] at h
  linarith

theorem row1397 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6834 + (1 : ℝ) * HLm Γ 5 L6836 + (-1 : ℝ) * HLm Γ 5 L6838 + (-1 : ℝ) * HLm Γ 5 L147 := by
  have h := HLm_submod hΓ [F67] L147 [F85]
  rw [show [F67] ++ L147 ++ [F85] = L6839 from rfl, show [F67] ++ L147 = L6835 from rfl,
    show L147 ++ [F85] = L6837 from rfl] at h
  rw [i4072 hinj, i4070 hinj, i4071 hinj] at h
  linarith

theorem row1398 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6840 + (1 : ℝ) * HLm Γ 5 L6836 + (-1 : ℝ) * HLm Γ 5 L6842 + (-1 : ℝ) * HLm Γ 5 L147 := by
  have h := HLm_submod hΓ [F68] L147 [F85]
  rw [show [F68] ++ L147 ++ [F85] = L6843 from rfl, show [F68] ++ L147 = L6841 from rfl,
    show L147 ++ [F85] = L6837 from rfl] at h
  rw [i4074 hinj, i4073 hinj, i4071 hinj] at h
  linarith

theorem row1399 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6844 + (1 : ℝ) * HLm Γ 5 L739 + (-1 : ℝ) * HLm Γ 5 L6846 + (-1 : ℝ) * HLm Γ 5 L147 := by
  have h := HLm_submod hΓ [F23] L147 [F27]
  rw [show [F23] ++ L147 ++ [F27] = L6847 from rfl, show [F23] ++ L147 = L6845 from rfl,
    show L147 ++ [F27] = L740 from rfl] at h
  rw [i4076 hinj, i4075 hinj, i325 hinj] at h
  linarith

theorem row1400 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6848 + (1 : ℝ) * HLm Γ 5 L2004 + (-1 : ℝ) * HLm Γ 5 L6850 + (-1 : ℝ) * HLm Γ 5 L147 := by
  have h := HLm_submod hΓ [F210] L147 [F45]
  rw [show [F210] ++ L147 ++ [F45] = L6851 from rfl, show [F210] ++ L147 = L6849 from rfl,
    show L147 ++ [F45] = L2004 from rfl] at h
  rw [i4078 hinj, i4077 hinj] at h
  linarith

theorem row1401 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6848 + (1 : ℝ) * HLm Γ 5 L6852 + (-1 : ℝ) * HLm Γ 5 L6853 + (-1 : ℝ) * HLm Γ 5 L147 := by
  have h := HLm_submod hΓ [F210] L147 [F6]
  rw [show [F210] ++ L147 ++ [F6] = L6854 from rfl, show [F210] ++ L147 = L6849 from rfl,
    show L147 ++ [F6] = L6852 from rfl] at h
  rw [i4079 hinj, i4077 hinj] at h
  linarith

theorem row1402 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6855 + (1 : ℝ) * HLm Γ 5 L2837 + (-1 : ℝ) * HLm Γ 5 L6857 + (-1 : ℝ) * HLm Γ 5 L147 := by
  have h := HLm_submod hΓ [F25] L147 [F217]
  rw [show [F25] ++ L147 ++ [F217] = L6858 from rfl, show [F25] ++ L147 = L6856 from rfl,
    show L147 ++ [F217] = L2837 from rfl] at h
  rw [i4081 hinj, i4080 hinj] at h
  linarith

theorem row1403 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L26 + (1 : ℝ) * HLm Γ 5 L6859 + (-1 : ℝ) * HLm Γ 5 L6860 + (-1 : ℝ) * HLm Γ 5 L22 := by
  have h := HLm_submod hΓ [F0] L22 [F217]
  rw [show [F0] ++ L22 ++ [F217] = L6861 from rfl, show [F0] ++ L22 = L154 from rfl,
    show L22 ++ [F217] = L6859 from rfl] at h
  rw [i4082 hinj, i49 hinj] at h
  linarith

theorem row1404 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2010 + (1 : ℝ) * HLm Γ 5 L159 + (-1 : ℝ) * HLm Γ 5 L6862 + (-1 : ℝ) * HLm Γ 5 L22 := by
  have h := HLm_submod hΓ [F1] L22 [F21]
  rw [show [F1] ++ L22 ++ [F21] = L6863 from rfl, show [F1] ++ L22 = L2011 from rfl,
    show L22 ++ [F21] = L763 from rfl] at h
  rw [i4083 hinj, i1101 hinj, i337 hinj] at h
  linarith

theorem row1405 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2010 + (1 : ℝ) * HLm Γ 5 L6859 + (-1 : ℝ) * HLm Γ 5 L6864 + (-1 : ℝ) * HLm Γ 5 L22 := by
  have h := HLm_submod hΓ [F1] L22 [F217]
  rw [show [F1] ++ L22 ++ [F217] = L6865 from rfl, show [F1] ++ L22 = L2011 from rfl,
    show L22 ++ [F217] = L6859 from rfl] at h
  rw [i4084 hinj, i1101 hinj] at h
  linarith

theorem row1406 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L705 + (1 : ℝ) * HLm Γ 5 L6859 + (-1 : ℝ) * HLm Γ 5 L6866 + (-1 : ℝ) * HLm Γ 5 L22 := by
  have h := HLm_submod hΓ [F51] L22 [F217]
  rw [show [F51] ++ L22 ++ [F217] = L6867 from rfl, show [F51] ++ L22 = L706 from rfl,
    show L22 ++ [F217] = L6859 from rfl] at h
  rw [i4085 hinj, i309 hinj] at h
  linarith

theorem row1407 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6868 + (1 : ℝ) * HLm Γ 5 L6859 + (-1 : ℝ) * HLm Γ 5 L6870 + (-1 : ℝ) * HLm Γ 5 L22 := by
  have h := HLm_submod hΓ [F47] L22 [F217]
  rw [show [F47] ++ L22 ++ [F217] = L6871 from rfl, show [F47] ++ L22 = L6869 from rfl,
    show L22 ++ [F217] = L6859 from rfl] at h
  rw [i4087 hinj, i4086 hinj] at h
  linarith

theorem row1408 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6872 + (1 : ℝ) * HLm Γ 5 L827 + (-1 : ℝ) * HLm Γ 5 L6874 + (-1 : ℝ) * HLm Γ 5 L22 := by
  have h := HLm_submod hΓ [F210] L22 [F6]
  rw [show [F210] ++ L22 ++ [F6] = L6875 from rfl, show [F210] ++ L22 = L6873 from rfl,
    show L22 ++ [F6] = L827 from rfl] at h
  rw [i4089 hinj, i4088 hinj] at h
  linarith

theorem row1409 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6876 + (1 : ℝ) * HLm Γ 5 L827 + (-1 : ℝ) * HLm Γ 5 L6878 + (-1 : ℝ) * HLm Γ 5 L22 := by
  have h := HLm_submod hΓ [F236] L22 [F6]
  rw [show [F236] ++ L22 ++ [F6] = L6879 from rfl, show [F236] ++ L22 = L6877 from rfl,
    show L22 ++ [F6] = L827 from rfl] at h
  rw [i4091 hinj, i4090 hinj] at h
  linarith

theorem row1410 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L686 + (1 : ℝ) * HLm Γ 5 L576 + (-1 : ℝ) * HLm Γ 5 L578 + (-1 : ℝ) * HLm Γ 5 L26 := by
  have h := HLm_submod hΓ [F3] L27 [F16]
  rw [show [F3] ++ L27 ++ [F16] = L6882 from rfl, show [F3] ++ L27 = L6880 from rfl,
    show L27 ++ [F16] = L6881 from rfl] at h
  rw [i4094 hinj, i4092 hinj, i4093 hinj, i5 hinj] at h
  linarith

theorem row1411 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L679 + (1 : ℝ) * HLm Γ 5 L2899 + (-1 : ℝ) * HLm Γ 5 L6884 + (-1 : ℝ) * HLm Γ 5 L26 := by
  have h := HLm_submod hΓ [F6] L27 [F219]
  rw [show [F6] ++ L27 ++ [F219] = L6885 from rfl, show [F6] ++ L27 = L6883 from rfl,
    show L27 ++ [F219] = L6792 from rfl] at h
  rw [i4096 hinj, i4095 hinj, i4047 hinj, i5 hinj] at h
  linarith

theorem row1412 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L178 + (1 : ℝ) * HLm Γ 5 L2910 + (-1 : ℝ) * HLm Γ 5 L3312 + (-1 : ℝ) * HLm Γ 5 L31 := by
  have h := HLm_submod hΓ [F7] L31 [F217]
  rw [show [F7] ++ L31 ++ [F217] = L3313 from rfl, show [F7] ++ L31 = L179 from rfl,
    show L31 ++ [F217] = L2910 from rfl] at h
  rw [i1866 hinj, i61 hinj] at h
  linarith

theorem row1413 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2014 + (1 : ℝ) * HLm Γ 5 L3213 + (-1 : ℝ) * HLm Γ 5 L6886 + (-1 : ℝ) * HLm Γ 5 L5 := by
  have h := HLm_submod hΓ [F9] L5 [F218]
  rw [show [F9] ++ L5 ++ [F218] = L6887 from rfl, show [F9] ++ L5 = L2014 from rfl,
    show L5 ++ [F218] = L3214 from rfl] at h
  rw [i4097 hinj, i1816 hinj] at h
  linarith

theorem row1414 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L686 + (1 : ℝ) * HLm Γ 5 L3179 + (-1 : ℝ) * HLm Γ 5 L839 + (-1 : ℝ) * HLm Γ 5 L5 := by
  have h := HLm_submod hΓ [F10] L5 [F6]
  rw [show [F10] ++ L5 ++ [F6] = L4951 from rfl, show [F10] ++ L5 = L6888 from rfl,
    show L5 ++ [F6] = L6889 from rfl] at h
  rw [i2791 hinj, i4098 hinj, i4099 hinj] at h
  linarith

theorem row1415 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L94 + (1 : ℝ) * HLm Γ 5 L6890 + (-1 : ℝ) * HLm Γ 5 L6891 + (-1 : ℝ) * HLm Γ 5 L199 := by
  have h := HLm_submod hΓ [F0] L199 [F217]
  rw [show [F0] ++ L199 ++ [F217] = L6891 from rfl, show [F0] ++ L199 = L94 from rfl,
    show L199 ++ [F217] = L6890 from rfl] at h
  linarith

theorem row1416 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L17 + (1 : ℝ) * HLm Γ 5 L6890 + (-1 : ℝ) * HLm Γ 5 L6893 + (-1 : ℝ) * HLm Γ 5 L199 := by
  have h := HLm_submod hΓ [F62] L199 [F217]
  rw [show [F62] ++ L199 ++ [F217] = L6894 from rfl, show [F62] ++ L199 = L6892 from rfl,
    show L199 ++ [F217] = L6890 from rfl] at h
  rw [i4101 hinj, i4100 hinj] at h
  linarith

theorem row1417 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6895 + (1 : ℝ) * HLm Γ 5 L6890 + (-1 : ℝ) * HLm Γ 5 L6896 + (-1 : ℝ) * HLm Γ 5 L199 := by
  have h := HLm_submod hΓ [F47] L199 [F217]
  rw [show [F47] ++ L199 ++ [F217] = L6896 from rfl, show [F47] ++ L199 = L6895 from rfl,
    show L199 ++ [F217] = L6890 from rfl] at h
  linarith

theorem row1418 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6897 + (1 : ℝ) * HLm Γ 5 L196 + (-1 : ℝ) * HLm Γ 5 L6899 + (-1 : ℝ) * HLm Γ 5 L199 := by
  have h := HLm_submod hΓ [F210] L199 [F45]
  rw [show [F210] ++ L199 ++ [F45] = L6900 from rfl, show [F210] ++ L199 = L6898 from rfl,
    show L199 ++ [F45] = L196 from rfl] at h
  rw [i4103 hinj, i4102 hinj] at h
  linarith

theorem row1419 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2078 + (1 : ℝ) * HLm Γ 5 L6902 + (-1 : ℝ) * HLm Γ 5 L6904 + (-1 : ℝ) * HLm Γ 5 L199 := by
  have h := HLm_submod hΓ [F25] L199 [F85]
  rw [show [F25] ++ L199 ++ [F85] = L6905 from rfl, show [F25] ++ L199 = L6901 from rfl,
    show L199 ++ [F85] = L6903 from rfl] at h
  rw [i4106 hinj, i4104 hinj, i4105 hinj] at h
  linarith

theorem row1420 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L205 + (1 : ℝ) * HLm Γ 5 L6794 + (-1 : ℝ) * HLm Γ 5 L6906 + (-1 : ℝ) * HLm Γ 5 L204 := by
  have h := HLm_submod hΓ [F47] L204 [F219]
  rw [show [F47] ++ L204 ++ [F219] = L6907 from rfl, show [F47] ++ L204 = L205 from rfl,
    show L204 ++ [F219] = L6794 from rfl] at h
  rw [i4107 hinj] at h
  linarith

theorem row1421 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L485 + (1 : ℝ) * HLm Γ 5 L6908 + (-1 : ℝ) * HLm Γ 5 L6910 + (-1 : ℝ) * HLm Γ 5 L38 := by
  have h := HLm_submod hΓ [F68] L38 [F214]
  rw [show [F68] ++ L38 ++ [F214] = L6911 from rfl, show [F68] ++ L38 = L485 from rfl,
    show L38 ++ [F214] = L6909 from rfl] at h
  rw [i4109 hinj, i4108 hinj] at h
  linarith

theorem row1422 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1968 + (1 : ℝ) * HLm Γ 5 L3797 + (-1 : ℝ) * HLm Γ 5 L3788 + (-1 : ℝ) * HLm Γ 5 L38 := by
  have h := HLm_submod hΓ [F25] L38 [F217]
  rw [show [F25] ++ L38 ++ [F217] = L6912 from rfl, show [F25] ++ L38 = L1968 from rfl,
    show L38 ++ [F217] = L3798 from rfl] at h
  rw [i4110 hinj, i2123 hinj] at h
  linarith

theorem row1423 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3088 + (1 : ℝ) * HLm Γ 5 L576 + (-1 : ℝ) * HLm Γ 5 L767 + (-1 : ℝ) * HLm Γ 5 L53 := by
  have h := HLm_submod hΓ [F2] L53 [F10]
  rw [show [F2] ++ L53 ++ [F10] = L6915 from rfl, show [F2] ++ L53 = L6913 from rfl,
    show L53 ++ [F10] = L6914 from rfl] at h
  rw [i4113 hinj, i4111 hinj, i4112 hinj] at h
  linarith

theorem row1424 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L25 + (1 : ℝ) * HLm Γ 5 L2971 + (-1 : ℝ) * HLm Γ 5 L1594 + (-1 : ℝ) * HLm Γ 5 L11 := by
  have h := HLm_submod hΓ [F9] L11 [F43]
  rw [show [F9] ++ L11 ++ [F43] = L1595 from rfl, show [F9] ++ L11 = L25 from rfl,
    show L11 ++ [F43] = L2972 from rfl] at h
  rw [i817 hinj, i1694 hinj] at h
  linarith

theorem row1425 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6916 + (1 : ℝ) * HLm Γ 5 L6918 + (-1 : ℝ) * HLm Γ 5 L6920 + (-1 : ℝ) * HLm Γ 5 L11 := by
  have h := HLm_submod hΓ [F67] L11 [F25]
  rw [show [F67] ++ L11 ++ [F25] = L6921 from rfl, show [F67] ++ L11 = L6917 from rfl,
    show L11 ++ [F25] = L6919 from rfl] at h
  rw [i4116 hinj, i4114 hinj, i4115 hinj] at h
  linarith

theorem row1426 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6922 + (1 : ℝ) * HLm Γ 5 L2976 + (-1 : ℝ) * HLm Γ 5 L6923 + (-1 : ℝ) * HLm Γ 5 L11 := by
  have h := HLm_submod hΓ [F17] L11 [F218]
  rw [show [F17] ++ L11 ++ [F218] = L6924 from rfl, show [F17] ++ L11 = L6922 from rfl,
    show L11 ++ [F218] = L2977 from rfl] at h
  rw [i4117 hinj, i1697 hinj] at h
  linarith

theorem row1427 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L241 + (1 : ℝ) * HLm Γ 5 L329 + (-1 : ℝ) * HLm Γ 5 L2068 + (-1 : ℝ) * HLm Γ 5 L2848 := by
  have h := HLm_submod hΓ [F22] L2848 [F86]
  rw [show [F22] ++ L2848 ++ [F86] = L6925 from rfl, show [F22] ++ L2848 = L241 from rfl,
    show L2848 ++ [F86] = L2982 from rfl] at h
  rw [i4118 hinj, i1700 hinj] at h
  linarith

theorem row1428 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3879 + (1 : ℝ) * HLm Γ 5 L2126 + (-1 : ℝ) * HLm Γ 5 L6926 + (-1 : ℝ) * HLm Γ 5 L2848 := by
  have h := HLm_submod hΓ [F211] L2848 [F34]
  rw [show [F211] ++ L2848 ++ [F34] = L6927 from rfl, show [F211] ++ L2848 = L3879 from rfl,
    show L2848 ++ [F34] = L2986 from rfl] at h
  rw [i4119 hinj, i1702 hinj] at h
  linarith

theorem row1429 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6928 + (1 : ℝ) * HLm Γ 5 L329 + (-1 : ℝ) * HLm Γ 5 L6929 + (-1 : ℝ) * HLm Γ 5 L2848 := by
  have h := HLm_submod hΓ [F228] L2848 [F86]
  rw [show [F228] ++ L2848 ++ [F86] = L6930 from rfl, show [F228] ++ L2848 = L6928 from rfl,
    show L2848 ++ [F86] = L2982 from rfl] at h
  rw [i4120 hinj, i1700 hinj] at h
  linarith

theorem row1430 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6931 + (1 : ℝ) * HLm Γ 5 L400 + (-1 : ℝ) * HLm Γ 5 L2210 + (-1 : ℝ) * HLm Γ 5 L2998 := by
  have h := HLm_submod hΓ [F0] L2998 [F34]
  rw [show [F0] ++ L2998 ++ [F34] = L3922 from rfl, show [F0] ++ L2998 = L6932 from rfl,
    show L2998 ++ [F34] = L400 from rfl] at h
  rw [i2190 hinj, i4121 hinj] at h
  linarith

theorem row1431 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6933 + (1 : ℝ) * HLm Γ 5 L6935 + (-1 : ℝ) * HLm Γ 5 L6937 + (-1 : ℝ) * HLm Γ 5 L6939 := by
  have h := HLm_submod hΓ [F210] L6939 [F34]
  rw [show [F210] ++ L6939 ++ [F34] = L6938 from rfl, show [F210] ++ L6939 = L6934 from rfl,
    show L6939 ++ [F34] = L6936 from rfl] at h
  rw [i4124 hinj, i4122 hinj, i4123 hinj] at h
  linarith

theorem row1432 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6940 + (1 : ℝ) * HLm Γ 5 L6942 + (-1 : ℝ) * HLm Γ 5 L6944 + (-1 : ℝ) * HLm Γ 5 L2850 := by
  have h := HLm_submod hΓ [F210] L2850 [F90]
  rw [show [F210] ++ L2850 ++ [F90] = L6945 from rfl, show [F210] ++ L2850 = L6941 from rfl,
    show L2850 ++ [F90] = L6943 from rfl] at h
  rw [i4127 hinj, i4125 hinj, i4126 hinj] at h
  linarith

theorem row1433 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6946 + (1 : ℝ) * HLm Γ 5 L3001 + (-1 : ℝ) * HLm Γ 5 L3985 + (-1 : ℝ) * HLm Γ 5 L2850 := by
  have h := HLm_submod hΓ [F228] L2850 [F55]
  rw [show [F228] ++ L2850 ++ [F55] = L6948 from rfl, show [F228] ++ L2850 = L6947 from rfl,
    show L2850 ++ [F55] = L3002 from rfl] at h
  rw [i4129 hinj, i4128 hinj, i1710 hinj] at h
  linarith

theorem row1434 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6949 + (1 : ℝ) * HLm Γ 5 L6951 + (-1 : ℝ) * HLm Γ 5 L6952 + (-1 : ℝ) * HLm Γ 5 L3014 := by
  have h := HLm_submod hΓ [F25] L3014 [F45]
  rw [show [F25] ++ L3014 ++ [F45] = L6953 from rfl, show [F25] ++ L3014 = L6950 from rfl,
    show L3014 ++ [F45] = L6951 from rfl] at h
  rw [i4131 hinj, i4130 hinj] at h
  linarith

theorem row1435 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L252 + (1 : ℝ) * HLm Γ 5 L40 + (-1 : ℝ) * HLm Γ 5 L550 + (-1 : ℝ) * HLm Γ 5 L39 := by
  have h := HLm_submod hΓ [F0] L39 [F16]
  rw [show [F0] ++ L39 ++ [F16] = L6954 from rfl, show [F0] ++ L39 = L253 from rfl,
    show L39 ++ [F16] = L40 from rfl] at h
  rw [i4132 hinj, i92 hinj] at h
  linarith

theorem row1436 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L258 + (1 : ℝ) * HLm Γ 5 L273 + (-1 : ℝ) * HLm Γ 5 L6955 + (-1 : ℝ) * HLm Γ 5 L39 := by
  have h := HLm_submod hΓ [F1] L39 [F45]
  rw [show [F1] ++ L39 ++ [F45] = L6956 from rfl, show [F1] ++ L39 = L259 from rfl,
    show L39 ++ [F45] = L273 from rfl] at h
  rw [i4133 hinj, i95 hinj] at h
  linarith

theorem row1437 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L113 + (1 : ℝ) * HLm Γ 5 L273 + (-1 : ℝ) * HLm Γ 5 L6957 + (-1 : ℝ) * HLm Γ 5 L39 := by
  have h := HLm_submod hΓ [F7] L39 [F45]
  rw [show [F7] ++ L39 ++ [F45] = L6958 from rfl, show [F7] ++ L39 = L262 from rfl,
    show L39 ++ [F45] = L273 from rfl] at h
  rw [i4134 hinj, i97 hinj] at h
  linarith

theorem row1438 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L265 + (1 : ℝ) * HLm Γ 5 L6959 + (-1 : ℝ) * HLm Γ 5 L6960 + (-1 : ℝ) * HLm Γ 5 L39 := by
  have h := HLm_submod hΓ [F2] L39 [F217]
  rw [show [F2] ++ L39 ++ [F217] = L6961 from rfl, show [F2] ++ L39 = L266 from rfl,
    show L39 ++ [F217] = L6959 from rfl] at h
  rw [i4135 hinj, i99 hinj] at h
  linarith

theorem row1439 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3015 + (1 : ℝ) * HLm Γ 5 L404 + (-1 : ℝ) * HLm Γ 5 L6963 + (-1 : ℝ) * HLm Γ 5 L39 := by
  have h := HLm_submod hΓ [F67] L39 [F30]
  rw [show [F67] ++ L39 ++ [F30] = L6964 from rfl, show [F67] ++ L39 = L3016 from rfl,
    show L39 ++ [F30] = L6962 from rfl] at h
  rw [i4137 hinj, i1716 hinj, i4136 hinj] at h
  linarith

theorem row1440 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3015 + (1 : ℝ) * HLm Γ 5 L6965 + (-1 : ℝ) * HLm Γ 5 L6967 + (-1 : ℝ) * HLm Γ 5 L39 := by
  have h := HLm_submod hΓ [F67] L39 [F96]
  rw [show [F67] ++ L39 ++ [F96] = L6968 from rfl, show [F67] ++ L39 = L3016 from rfl,
    show L39 ++ [F96] = L6966 from rfl] at h
  rw [i4139 hinj, i1716 hinj, i4138 hinj] at h
  linarith

theorem row1441 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3015 + (1 : ℝ) * HLm Γ 5 L6969 + (-1 : ℝ) * HLm Γ 5 L6971 + (-1 : ℝ) * HLm Γ 5 L39 := by
  have h := HLm_submod hΓ [F67] L39 [F85]
  rw [show [F67] ++ L39 ++ [F85] = L6972 from rfl, show [F67] ++ L39 = L3016 from rfl,
    show L39 ++ [F85] = L6970 from rfl] at h
  rw [i4141 hinj, i1716 hinj, i4140 hinj] at h
  linarith

theorem row1442 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6973 + (1 : ℝ) * HLm Γ 5 L273 + (-1 : ℝ) * HLm Γ 5 L6975 + (-1 : ℝ) * HLm Γ 5 L39 := by
  have h := HLm_submod hΓ [F210] L39 [F45]
  rw [show [F210] ++ L39 ++ [F45] = L6976 from rfl, show [F210] ++ L39 = L6974 from rfl,
    show L39 ++ [F45] = L273 from rfl] at h
  rw [i4143 hinj, i4142 hinj] at h
  linarith

theorem row1443 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3032 + (1 : ℝ) * HLm Γ 5 L3028 + (-1 : ℝ) * HLm Γ 5 L6977 + (-1 : ℝ) * HLm Γ 5 L59 := by
  have h := HLm_submod hΓ [F3] L59 [F218]
  rw [show [F3] ++ L59 ++ [F218] = L6978 from rfl, show [F3] ++ L59 = L3033 from rfl,
    show L59 ++ [F218] = L3029 from rfl] at h
  rw [i4144 hinj, i1724 hinj, i1722 hinj] at h
  linarith

theorem row1444 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L297 + (1 : ℝ) * HLm Γ 5 L320 + (-1 : ℝ) * HLm Γ 5 L6979 + (-1 : ℝ) * HLm Γ 5 L63 := by
  have h := HLm_submod hΓ [F1] L63 [F67]
  rw [show [F1] ++ L63 ++ [F67] = L6980 from rfl, show [F1] ++ L63 = L298 from rfl,
    show L63 ++ [F67] = L320 from rfl] at h
  rw [i4145 hinj, i114 hinj] at h
  linarith

theorem row1445 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L297 + (1 : ℝ) * HLm Γ 5 L314 + (-1 : ℝ) * HLm Γ 5 L6981 + (-1 : ℝ) * HLm Γ 5 L63 := by
  have h := HLm_submod hΓ [F1] L63 [F45]
  rw [show [F1] ++ L63 ++ [F45] = L6982 from rfl, show [F1] ++ L63 = L298 from rfl,
    show L63 ++ [F45] = L315 from rfl] at h
  rw [i4146 hinj, i114 hinj, i122 hinj] at h
  linarith

theorem row1446 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L126 + (1 : ℝ) * HLm Γ 5 L307 + (-1 : ℝ) * HLm Γ 5 L3558 + (-1 : ℝ) * HLm Γ 5 L63 := by
  have h := HLm_submod hΓ [F2] L63 [F9]
  rw [show [F2] ++ L63 ++ [F9] = L6983 from rfl, show [F2] ++ L63 = L2835 from rfl,
    show L63 ++ [F9] = L3041 from rfl] at h
  rw [i4147 hinj, i1628 hinj, i1729 hinj] at h
  linarith

theorem row1447 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L312 + (1 : ℝ) * HLm Γ 5 L3974 + (-1 : ℝ) * HLm Γ 5 L3968 + (-1 : ℝ) * HLm Γ 5 L63 := by
  have h := HLm_submod hΓ [F3] L63 [F68]
  rw [show [F3] ++ L63 ++ [F68] = L6985 from rfl, show [F3] ++ L63 = L313 from rfl,
    show L63 ++ [F68] = L6984 from rfl] at h
  rw [i4149 hinj, i121 hinj, i4148 hinj] at h
  linarith

theorem row1448 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6986 + (1 : ℝ) * HLm Γ 5 L320 + (-1 : ℝ) * HLm Γ 5 L6988 + (-1 : ℝ) * HLm Γ 5 L63 := by
  have h := HLm_submod hΓ [F44] L63 [F67]
  rw [show [F44] ++ L63 ++ [F67] = L6989 from rfl, show [F44] ++ L63 = L6987 from rfl,
    show L63 ++ [F67] = L320 from rfl] at h
  rw [i4151 hinj, i4150 hinj] at h
  linarith

theorem row1449 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L320 + (1 : ℝ) * HLm Γ 5 L6991 + (-1 : ℝ) * HLm Γ 5 L5207 + (-1 : ℝ) * HLm Γ 5 L63 := by
  have h := HLm_submod hΓ [F67] L63 [F236]
  rw [show [F67] ++ L63 ++ [F236] = L6992 from rfl, show [F67] ++ L63 = L6990 from rfl,
    show L63 ++ [F236] = L6991 from rfl] at h
  rw [i4153 hinj, i4152 hinj] at h
  linarith

theorem row1450 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6993 + (1 : ℝ) * HLm Γ 5 L314 + (-1 : ℝ) * HLm Γ 5 L6995 + (-1 : ℝ) * HLm Γ 5 L63 := by
  have h := HLm_submod hΓ [F214] L63 [F45]
  rw [show [F214] ++ L63 ++ [F45] = L6996 from rfl, show [F214] ++ L63 = L6994 from rfl,
    show L63 ++ [F45] = L315 from rfl] at h
  rw [i4155 hinj, i4154 hinj, i122 hinj] at h
  linarith

theorem row1451 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6997 + (1 : ℝ) * HLm Γ 5 L329 + (-1 : ℝ) * HLm Γ 5 L6999 + (-1 : ℝ) * HLm Γ 5 L332 := by
  have h := HLm_submod hΓ [F7] L332 [F67]
  rw [show [F7] ++ L332 ++ [F67] = L7000 from rfl, show [F7] ++ L332 = L6998 from rfl,
    show L332 ++ [F67] = L329 from rfl] at h
  rw [i4157 hinj, i4156 hinj] at h
  linarith

theorem row1452 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7001 + (1 : ℝ) * HLm Γ 5 L2855 + (-1 : ℝ) * HLm Γ 5 L7003 + (-1 : ℝ) * HLm Γ 5 L332 := by
  have h := HLm_submod hΓ [F9] L332 [F23]
  rw [show [F9] ++ L332 ++ [F23] = L7004 from rfl, show [F9] ++ L332 = L7002 from rfl,
    show L332 ++ [F23] = L2855 from rfl] at h
  rw [i4159 hinj, i4158 hinj] at h
  linarith

theorem row1453 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L329 + (1 : ℝ) * HLm Γ 5 L7005 + (-1 : ℝ) * HLm Γ 5 L7007 + (-1 : ℝ) * HLm Γ 5 L332 := by
  have h := HLm_submod hΓ [F67] L332 [F236]
  rw [show [F67] ++ L332 ++ [F236] = L7008 from rfl, show [F67] ++ L332 = L2982 from rfl,
    show L332 ++ [F236] = L7006 from rfl] at h
  rw [i4161 hinj, i1700 hinj, i4160 hinj] at h
  linarith

theorem row1454 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7009 + (1 : ℝ) * HLm Γ 5 L7011 + (-1 : ℝ) * HLm Γ 5 L7013 + (-1 : ℝ) * HLm Γ 5 L68 := by
  have h := HLm_submod hΓ [F108] L68 [F218]
  rw [show [F108] ++ L68 ++ [F218] = L7014 from rfl, show [F108] ++ L68 = L7010 from rfl,
    show L68 ++ [F218] = L7012 from rfl] at h
  rw [i4164 hinj, i4162 hinj, i4163 hinj] at h
  linarith

theorem row1455 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7015 + (1 : ℝ) * HLm Γ 5 L2098 + (-1 : ℝ) * HLm Γ 5 L7017 + (-1 : ℝ) * HLm Γ 5 L68 := by
  have h := HLm_submod hΓ [F228] L68 [F45]
  rw [show [F228] ++ L68 ++ [F45] = L7018 from rfl, show [F228] ++ L68 = L7016 from rfl,
    show L68 ++ [F45] = L2099 from rfl] at h
  rw [i4166 hinj, i4165 hinj, i1152 hinj] at h
  linarith

theorem row1456 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7019 + (1 : ℝ) * HLm Γ 5 L384 + (-1 : ℝ) * HLm Γ 5 L7020 + (-1 : ℝ) * HLm Γ 5 L387 := by
  have h := HLm_submod hΓ [F21] L387 [F67]
  rw [show [F21] ++ L387 ++ [F67] = L7020 from rfl, show [F21] ++ L387 = L7019 from rfl,
    show L387 ++ [F67] = L384 from rfl] at h
  linarith

theorem row1457 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L74 + (1 : ℝ) * HLm Γ 5 L390 + (-1 : ℝ) * HLm Γ 5 L1458 + (-1 : ℝ) * HLm Γ 5 L72 := by
  have h := HLm_submod hΓ [F10] L72 [F67]
  rw [show [F10] ++ L72 ++ [F67] = L7022 from rfl, show [F10] ++ L72 = L7021 from rfl,
    show L72 ++ [F67] = L390 from rfl] at h
  rw [i4168 hinj, i4167 hinj] at h
  linarith

theorem row1458 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3643 + (1 : ℝ) * HLm Γ 5 L7024 + (-1 : ℝ) * HLm Γ 5 L7026 + (-1 : ℝ) * HLm Γ 5 L72 := by
  have h := HLm_submod hΓ [F12] L72 [F218]
  rw [show [F12] ++ L72 ++ [F218] = L7027 from rfl, show [F12] ++ L72 = L7023 from rfl,
    show L72 ++ [F218] = L7025 from rfl] at h
  rw [i4171 hinj, i4169 hinj, i4170 hinj] at h
  linarith

theorem row1459 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L390 + (1 : ℝ) * HLm Γ 5 L7028 + (-1 : ℝ) * HLm Γ 5 L7030 + (-1 : ℝ) * HLm Γ 5 L72 := by
  have h := HLm_submod hΓ [F67] L72 [F236]
  rw [show [F67] ++ L72 ++ [F236] = L7031 from rfl, show [F67] ++ L72 = L2849 from rfl,
    show L72 ++ [F236] = L7029 from rfl] at h
  rw [i4173 hinj, i1632 hinj, i4172 hinj] at h
  linarith

theorem row1460 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L390 + (1 : ℝ) * HLm Γ 5 L3122 + (-1 : ℝ) * HLm Γ 5 L7032 + (-1 : ℝ) * HLm Γ 5 L72 := by
  have h := HLm_submod hΓ [F67] L72 [F228]
  rw [show [F67] ++ L72 ++ [F228] = L7033 from rfl, show [F67] ++ L72 = L2849 from rfl,
    show L72 ++ [F228] = L3122 from rfl] at h
  rw [i4174 hinj, i1632 hinj] at h
  linarith

theorem row1461 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7034 + (1 : ℝ) * HLm Γ 5 L7036 + (-1 : ℝ) * HLm Γ 5 L7038 + (-1 : ℝ) * HLm Γ 5 L72 := by
  have h := HLm_submod hΓ [F210] L72 [F6]
  rw [show [F210] ++ L72 ++ [F6] = L7039 from rfl, show [F210] ++ L72 = L7035 from rfl,
    show L72 ++ [F6] = L7037 from rfl] at h
  rw [i4177 hinj, i4175 hinj, i4176 hinj] at h
  linarith

theorem row1462 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7040 + (1 : ℝ) * HLm Γ 5 L7042 + (-1 : ℝ) * HLm Γ 5 L7044 + (-1 : ℝ) * HLm Γ 5 L73 := by
  have h := HLm_submod hΓ [F210] L73 [F43]
  rw [show [F210] ++ L73 ++ [F43] = L7045 from rfl, show [F210] ++ L73 = L7041 from rfl,
    show L73 ++ [F43] = L7043 from rfl] at h
  rw [i4180 hinj, i4178 hinj, i4179 hinj] at h
  linarith

theorem row1463 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7040 + (1 : ℝ) * HLm Γ 5 L394 + (-1 : ℝ) * HLm Γ 5 L7046 + (-1 : ℝ) * HLm Γ 5 L73 := by
  have h := HLm_submod hΓ [F210] L73 [F6]
  rw [show [F210] ++ L73 ++ [F6] = L7047 from rfl, show [F210] ++ L73 = L7041 from rfl,
    show L73 ++ [F6] = L395 from rfl] at h
  rw [i4181 hinj, i4178 hinj, i158 hinj] at h
  linarith

theorem row1464 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7048 + (1 : ℝ) * HLm Γ 5 L6795 + (-1 : ℝ) * HLm Γ 5 L2471 + (-1 : ℝ) * HLm Γ 5 L76 := by
  have h := HLm_submod hΓ [F0] L76 [F67]
  rw [show [F0] ++ L76 ++ [F67] = L2471 from rfl, show [F0] ++ L76 = L7048 from rfl,
    show L76 ++ [F67] = L6795 from rfl] at h
  linarith

theorem row1465 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7049 + (1 : ℝ) * HLm Γ 5 L6795 + (-1 : ℝ) * HLm Γ 5 L2462 + (-1 : ℝ) * HLm Γ 5 L76 := by
  have h := HLm_submod hΓ [F1] L76 [F67]
  rw [show [F1] ++ L76 ++ [F67] = L7051 from rfl, show [F1] ++ L76 = L7050 from rfl,
    show L76 ++ [F67] = L6795 from rfl] at h
  rw [i4183 hinj, i4182 hinj] at h
  linarith

theorem row1466 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7052 + (1 : ℝ) * HLm Γ 5 L6795 + (-1 : ℝ) * HLm Γ 5 L7054 + (-1 : ℝ) * HLm Γ 5 L76 := by
  have h := HLm_submod hΓ [F44] L76 [F67]
  rw [show [F44] ++ L76 ++ [F67] = L7055 from rfl, show [F44] ++ L76 = L7053 from rfl,
    show L76 ++ [F67] = L6795 from rfl] at h
  rw [i4185 hinj, i4184 hinj] at h
  linarith

theorem row1467 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6795 + (1 : ℝ) * HLm Γ 5 L7056 + (-1 : ℝ) * HLm Γ 5 L7058 + (-1 : ℝ) * HLm Γ 5 L76 := by
  have h := HLm_submod hΓ [F67] L76 [F211]
  rw [show [F67] ++ L76 ++ [F211] = L7059 from rfl, show [F67] ++ L76 = L6796 from rfl,
    show L76 ++ [F211] = L7057 from rfl] at h
  rw [i4187 hinj, i4049 hinj, i4186 hinj] at h
  linarith

theorem row1468 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7060 + (1 : ℝ) * HLm Γ 5 L7062 + (-1 : ℝ) * HLm Γ 5 L7064 + (-1 : ℝ) * HLm Γ 5 L420 := by
  have h := HLm_submod hΓ [F52] L420 [F214]
  rw [show [F52] ++ L420 ++ [F214] = L7065 from rfl, show [F52] ++ L420 = L7061 from rfl,
    show L420 ++ [F214] = L7063 from rfl] at h
  rw [i4190 hinj, i4188 hinj, i4189 hinj] at h
  linarith

theorem row1469 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L103 + (1 : ℝ) * HLm Γ 5 L439 + (-1 : ℝ) * HLm Γ 5 L106 + (-1 : ℝ) * HLm Γ 5 L427 := by
  have h := HLm_submod hΓ [F0] L428 [F23]
  rw [show [F0] ++ L428 ++ [F23] = L7067 from rfl, show [F0] ++ L428 = L2134 from rfl,
    show L428 ++ [F23] = L7066 from rfl] at h
  rw [i4192 hinj, i1169 hinj, i4191 hinj, i174 hinj] at h
  linarith

theorem row1470 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L168 + (1 : ℝ) * HLm Γ 5 L439 + (-1 : ℝ) * HLm Γ 5 L170 + (-1 : ℝ) * HLm Γ 5 L427 := by
  have h := HLm_submod hΓ [F9] L428 [F23]
  rw [show [F9] ++ L428 ++ [F23] = L7069 from rfl, show [F9] ++ L428 = L7068 from rfl,
    show L428 ++ [F23] = L7066 from rfl] at h
  rw [i4194 hinj, i4193 hinj, i4191 hinj, i174 hinj] at h
  linarith

theorem row1471 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L421 + (1 : ℝ) * HLm Γ 5 L2141 + (-1 : ℝ) * HLm Γ 5 L7071 + (-1 : ℝ) * HLm Γ 5 L427 := by
  have h := HLm_submod hΓ [F12] L428 [F67]
  rw [show [F12] ++ L428 ++ [F67] = L7072 from rfl, show [F12] ++ L428 = L422 from rfl,
    show L428 ++ [F67] = L7070 from rfl] at h
  rw [i4196 hinj, i171 hinj, i4195 hinj, i174 hinj] at h
  linarith

theorem row1472 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3140 + (1 : ℝ) * HLm Γ 5 L3215 + (-1 : ℝ) * HLm Γ 5 L7073 + (-1 : ℝ) * HLm Γ 5 L427 := by
  have h := HLm_submod hΓ [F43] L428 [F218]
  rw [show [F43] ++ L428 ++ [F218] = L7074 from rfl, show [F43] ++ L428 = L3141 from rfl,
    show L428 ++ [F218] = L4176 from rfl] at h
  rw [i4197 hinj, i1780 hinj, i2332 hinj, i174 hinj] at h
  linarith

theorem row1473 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7075 + (1 : ℝ) * HLm Γ 5 L3215 + (-1 : ℝ) * HLm Γ 5 L3735 + (-1 : ℝ) * HLm Γ 5 L427 := by
  have h := HLm_submod hΓ [F219] L428 [F218]
  rw [show [F219] ++ L428 ++ [F218] = L7077 from rfl, show [F219] ++ L428 = L7076 from rfl,
    show L428 ++ [F218] = L4176 from rfl] at h
  rw [i4199 hinj, i4198 hinj, i2332 hinj, i174 hinj] at h
  linarith

theorem row1474 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L327 + (1 : ℝ) * HLm Γ 5 L7078 + (-1 : ℝ) * HLm Γ 5 L7080 + (-1 : ℝ) * HLm Γ 5 L1955 := by
  have h := HLm_submod hΓ [F0] L1956 [F218]
  rw [show [F0] ++ L1956 ++ [F218] = L7081 from rfl, show [F0] ++ L1956 = L1957 from rfl,
    show L1956 ++ [F218] = L7079 from rfl] at h
  rw [i4201 hinj, i1080 hinj, i4200 hinj, i1079 hinj] at h
  linarith

theorem row1475 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L660 + (1 : ℝ) * HLm Γ 5 L7082 + (-1 : ℝ) * HLm Γ 5 L7084 + (-1 : ℝ) * HLm Γ 5 L1955 := by
  have h := HLm_submod hΓ [F7] L1956 [F219]
  rw [show [F7] ++ L1956 ++ [F219] = L7085 from rfl, show [F7] ++ L1956 = L661 from rfl,
    show L1956 ++ [F219] = L7083 from rfl] at h
  rw [i4203 hinj, i286 hinj, i4202 hinj, i1079 hinj] at h
  linarith

theorem row1476 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7086 + (1 : ℝ) * HLm Γ 5 L7088 + (-1 : ℝ) * HLm Γ 5 L7090 + (-1 : ℝ) * HLm Γ 5 L1955 := by
  have h := HLm_submod hΓ [F67] L1956 [F17]
  rw [show [F67] ++ L1956 ++ [F17] = L7091 from rfl, show [F67] ++ L1956 = L7087 from rfl,
    show L1956 ++ [F17] = L7089 from rfl] at h
  rw [i4206 hinj, i4204 hinj, i4205 hinj, i1079 hinj] at h
  linarith

theorem row1477 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L217 + (1 : ℝ) * HLm Γ 5 L273 + (-1 : ℝ) * HLm Γ 5 L220 + (-1 : ℝ) * HLm Γ 5 L456 := by
  have h := HLm_submod hΓ [F16] L456 [F17]
  rw [show [F16] ++ L456 ++ [F17] = L7093 from rfl, show [F16] ++ L456 = L451 from rfl,
    show L456 ++ [F17] = L7092 from rfl] at h
  rw [i4208 hinj, i186 hinj, i4207 hinj] at h
  linarith

theorem row1478 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2147 + (1 : ℝ) * HLm Γ 5 L6799 + (-1 : ℝ) * HLm Γ 5 L7095 + (-1 : ℝ) * HLm Γ 5 L456 := by
  have h := HLm_submod hΓ [F52] L456 [F36]
  rw [show [F52] ++ L456 ++ [F36] = L7096 from rfl, show [F52] ++ L456 = L2147 from rfl,
    show L456 ++ [F36] = L7094 from rfl] at h
  rw [i4210 hinj, i4209 hinj] at h
  linarith

theorem row1479 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6859 + (1 : ℝ) * HLm Γ 5 L7097 + (-1 : ℝ) * HLm Γ 5 L7099 + (-1 : ℝ) * HLm Γ 5 L2836 := by
  have h := HLm_submod hΓ [F9] L2836 [F108]
  rw [show [F9] ++ L2836 ++ [F108] = L7100 from rfl, show [F9] ++ L2836 = L6859 from rfl,
    show L2836 ++ [F108] = L7098 from rfl] at h
  rw [i4212 hinj, i4211 hinj] at h
  linarith

theorem row1480 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6859 + (1 : ℝ) * HLm Γ 5 L7101 + (-1 : ℝ) * HLm Γ 5 L7103 + (-1 : ℝ) * HLm Γ 5 L2836 := by
  have h := HLm_submod hΓ [F9] L2836 [F5]
  rw [show [F9] ++ L2836 ++ [F5] = L7104 from rfl, show [F9] ++ L2836 = L6859 from rfl,
    show L2836 ++ [F5] = L7102 from rfl] at h
  rw [i4214 hinj, i4213 hinj] at h
  linarith

theorem row1481 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2846 + (1 : ℝ) * HLm Γ 5 L3797 + (-1 : ℝ) * HLm Γ 5 L7106 + (-1 : ℝ) * HLm Γ 5 L2836 := by
  have h := HLm_submod hΓ [F46] L2836 [F16]
  rw [show [F46] ++ L2836 ++ [F16] = L7107 from rfl, show [F46] ++ L2836 = L2846 from rfl,
    show L2836 ++ [F16] = L7105 from rfl] at h
  rw [i4216 hinj, i4215 hinj] at h
  linarith

theorem row1482 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7101 + (1 : ℝ) * HLm Γ 5 L6959 + (-1 : ℝ) * HLm Γ 5 L7110 + (-1 : ℝ) * HLm Γ 5 L2836 := by
  have h := HLm_submod hΓ [F5] L2836 [F17]
  rw [show [F5] ++ L2836 ++ [F17] = L7111 from rfl, show [F5] ++ L2836 = L7108 from rfl,
    show L2836 ++ [F17] = L7109 from rfl] at h
  rw [i4219 hinj, i4217 hinj, i4218 hinj] at h
  linarith

theorem row1483 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2857 + (1 : ℝ) * HLm Γ 5 L3043 + (-1 : ℝ) * HLm Γ 5 L7113 + (-1 : ℝ) * HLm Γ 5 L2836 := by
  have h := HLm_submod hΓ [F25] L2836 [F27]
  rw [show [F25] ++ L2836 ++ [F27] = L7114 from rfl, show [F25] ++ L2836 = L2857 from rfl,
    show L2836 ++ [F27] = L7112 from rfl] at h
  rw [i4221 hinj, i4220 hinj] at h
  linarith

theorem row1484 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L526 + (1 : ℝ) * HLm Γ 5 L7115 + (-1 : ℝ) * HLm Γ 5 L7117 + (-1 : ℝ) * HLm Γ 5 L1958 := by
  have h := HLm_submod hΓ [F9] L1958 [F4]
  rw [show [F9] ++ L1958 ++ [F4] = L7118 from rfl, show [F9] ++ L1958 = L526 from rfl,
    show L1958 ++ [F4] = L7116 from rfl] at h
  rw [i4223 hinj, i4222 hinj] at h
  linarith

theorem row1485 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4061 + (1 : ℝ) * HLm Γ 5 L7119 + (-1 : ℝ) * HLm Γ 5 L7121 + (-1 : ℝ) * HLm Γ 5 L1958 := by
  have h := HLm_submod hΓ [F228] L1958 [F55]
  rw [show [F228] ++ L1958 ++ [F55] = L7122 from rfl, show [F228] ++ L1958 = L4061 from rfl,
    show L1958 ++ [F55] = L7120 from rfl] at h
  rw [i4225 hinj, i4224 hinj] at h
  linarith

theorem row1486 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L114 + (1 : ℝ) * HLm Γ 5 L3191 + (-1 : ℝ) * HLm Γ 5 L7123 + (-1 : ℝ) * HLm Γ 5 L13 := by
  have h := HLm_submod hΓ [F7] L13 [F210]
  rw [show [F7] ++ L13 ++ [F210] = L7123 from rfl, show [F7] ++ L13 = L114 from rfl,
    show L13 ++ [F210] = L3191 from rfl] at h
  linarith

theorem row1487 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L679 + (1 : ℝ) * HLm Γ 5 L4076 + (-1 : ℝ) * HLm Γ 5 L3279 + (-1 : ℝ) * HLm Γ 5 L13 := by
  have h := HLm_submod hΓ [F10] L13 [F214]
  rw [show [F10] ++ L13 ++ [F214] = L7125 from rfl, show [F10] ++ L13 = L1963 from rfl,
    show L13 ++ [F214] = L7124 from rfl] at h
  rw [i4227 hinj, i1083 hinj, i4226 hinj] at h
  linarith

theorem row1488 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7126 + (1 : ℝ) * HLm Γ 5 L445 + (-1 : ℝ) * HLm Γ 5 L7128 + (-1 : ℝ) * HLm Γ 5 L13 := by
  have h := HLm_submod hΓ [F82] L13 [F85]
  rw [show [F82] ++ L13 ++ [F85] = L7129 from rfl, show [F82] ++ L13 = L7126 from rfl,
    show L13 ++ [F85] = L7127 from rfl] at h
  rw [i4229 hinj, i4228 hinj] at h
  linarith

theorem row1489 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7130 + (1 : ℝ) * HLm Γ 5 L2872 + (-1 : ℝ) * HLm Γ 5 L7133 + (-1 : ℝ) * HLm Γ 5 L6791 := by
  have h := HLm_submod hΓ [F1] L6791 [F7]
  rw [show [F1] ++ L6791 ++ [F7] = L7134 from rfl, show [F1] ++ L6791 = L7131 from rfl,
    show L6791 ++ [F7] = L7132 from rfl] at h
  rw [i4232 hinj, i4230 hinj, i4231 hinj] at h
  linarith

theorem row1490 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2899 + (1 : ℝ) * HLm Γ 5 L2937 + (-1 : ℝ) * HLm Γ 5 L7136 + (-1 : ℝ) * HLm Γ 5 L6791 := by
  have h := HLm_submod hΓ [F10] L6791 [F3]
  rw [show [F10] ++ L6791 ++ [F3] = L7137 from rfl, show [F10] ++ L6791 = L6792 from rfl,
    show L6791 ++ [F3] = L7135 from rfl] at h
  rw [i4234 hinj, i4047 hinj, i4233 hinj] at h
  linarith

theorem row1491 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6794 + (1 : ℝ) * HLm Γ 5 L7082 + (-1 : ℝ) * HLm Γ 5 L7139 + (-1 : ℝ) * HLm Γ 5 L6791 := by
  have h := HLm_submod hΓ [F46] L6791 [F55]
  rw [show [F46] ++ L6791 ++ [F55] = L7140 from rfl, show [F46] ++ L6791 = L6794 from rfl,
    show L6791 ++ [F55] = L7138 from rfl] at h
  rw [i4236 hinj, i4235 hinj] at h
  linarith

theorem row1492 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7141 + (1 : ℝ) * HLm Γ 5 L3182 + (-1 : ℝ) * HLm Γ 5 L7142 + (-1 : ℝ) * HLm Γ 5 L6791 := by
  have h := HLm_submod hΓ [F211] L6791 [F6]
  rw [show [F211] ++ L6791 ++ [F6] = L7142 from rfl, show [F211] ++ L6791 = L7141 from rfl,
    show L6791 ++ [F6] = L3182 from rfl] at h
  linarith

theorem row1493 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9 + (1 : ℝ) * HLm Γ 5 L2919 + (-1 : ℝ) * HLm Γ 5 L2891 + (-1 : ℝ) * HLm Γ 5 L4 := by
  have h := HLm_submod hΓ [F1] L4 [F217]
  rw [show [F1] ++ L4 ++ [F217] = L7144 from rfl, show [F1] ++ L4 = L7143 from rfl,
    show L4 ++ [F217] = L2919 from rfl] at h
  rw [i4238 hinj, i4237 hinj] at h
  linarith

theorem row1494 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L552 + (1 : ℝ) * HLm Γ 5 L1266 + (-1 : ℝ) * HLm Γ 5 L5418 + (-1 : ℝ) * HLm Γ 5 L252 := by
  have h := HLm_submod hΓ [F67] L252 [F90]
  rw [show [F67] ++ L252 ++ [F90] = L7146 from rfl, show [F67] ++ L252 = L7145 from rfl,
    show L252 ++ [F90] = L1267 from rfl] at h
  rw [i4240 hinj, i4239 hinj, i618 hinj] at h
  linarith

theorem row1495 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7147 + (1 : ℝ) * HLm Γ 5 L7149 + (-1 : ℝ) * HLm Γ 5 L1332 + (-1 : ℝ) * HLm Γ 5 L6 := by
  have h := HLm_submod hΓ [F108] L6 [F68]
  rw [show [F108] ++ L6 ++ [F68] = L7151 from rfl, show [F108] ++ L6 = L7148 from rfl,
    show L6 ++ [F68] = L7150 from rfl] at h
  rw [i4243 hinj, i4241 hinj, i4242 hinj] at h
  linarith

theorem row1496 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7152 + (1 : ℝ) * HLm Γ 5 L7154 + (-1 : ℝ) * HLm Γ 5 L7155 + (-1 : ℝ) * HLm Γ 5 L6 := by
  have h := HLm_submod hΓ [F25] L6 [F217]
  rw [show [F25] ++ L6 ++ [F217] = L7156 from rfl, show [F25] ++ L6 = L7153 from rfl,
    show L6 ++ [F217] = L7154 from rfl] at h
  rw [i4245 hinj, i4244 hinj] at h
  linarith

theorem row1497 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7157 + (1 : ℝ) * HLm Γ 5 L7159 + (-1 : ℝ) * HLm Γ 5 L7160 + (-1 : ℝ) * HLm Γ 5 L94 := by
  have h := HLm_submod hΓ [F210] L94 [F43]
  rw [show [F210] ++ L94 ++ [F43] = L7161 from rfl, show [F210] ++ L94 = L7158 from rfl,
    show L94 ++ [F43] = L7159 from rfl] at h
  rw [i4247 hinj, i4246 hinj] at h
  linarith

theorem row1498 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1280 + (1 : ℝ) * HLm Γ 5 L7163 + (-1 : ℝ) * HLm Γ 5 L7165 + (-1 : ℝ) * HLm Γ 5 L103 := by
  have h := HLm_submod hΓ [F3] L103 [F217]
  rw [show [F3] ++ L103 ++ [F217] = L7166 from rfl, show [F3] ++ L103 = L7162 from rfl,
    show L103 ++ [F217] = L7164 from rfl] at h
  rw [i4250 hinj, i4248 hinj, i4249 hinj] at h
  linarith

theorem row1499 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1960 + (1 : ℝ) * HLm Γ 5 L7147 + (-1 : ℝ) * HLm Γ 5 L3316 + (-1 : ℝ) * HLm Γ 5 L575 := by
  have h := HLm_submod hΓ [F7] L575 [F3]
  rw [show [F7] ++ L575 ++ [F3] = L7169 from rfl, show [F7] ++ L575 = L7167 from rfl,
    show L575 ++ [F3] = L7168 from rfl] at h
  rw [i4253 hinj, i4251 hinj, i4252 hinj] at h
  linarith

end EntropyBounds.TwoSet.Certs.R7A5
