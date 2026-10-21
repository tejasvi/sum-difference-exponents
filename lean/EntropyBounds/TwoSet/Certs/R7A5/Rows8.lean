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

theorem row1200 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5990 + (1 : ℝ) * HLm Γ 5 L5992 + (-1 : ℝ) * HLm Γ 5 L5994 + (-1 : ℝ) * HLm Γ 5 L5996 := by
  have h := HLm_submod hΓ [F210] L5997 [F36]
  rw [show [F210] ++ L5997 ++ [F36] = L5995 from rfl, show [F210] ++ L5997 = L5991 from rfl,
    show L5997 ++ [F36] = L5993 from rfl] at h
  rw [i3423 hinj, i3421 hinj, i3422 hinj, i3424 hinj] at h
  linarith

theorem row1201 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4676 + (1 : ℝ) * HLm Γ 5 L5998 + (-1 : ℝ) * HLm Γ 5 L6000 + (-1 : ℝ) * HLm Γ 5 L4674 := by
  have h := HLm_submod hΓ [F7] L4675 [F16]
  rw [show [F7] ++ L4675 ++ [F16] = L6001 from rfl, show [F7] ++ L4675 = L4677 from rfl,
    show L4675 ++ [F16] = L5999 from rfl] at h
  rw [i3426 hinj, i2627 hinj, i3425 hinj, i2626 hinj] at h
  linarith

theorem row1202 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6002 + (1 : ℝ) * HLm Γ 5 L4684 + (-1 : ℝ) * HLm Γ 5 L6005 + (-1 : ℝ) * HLm Γ 5 L4682 := by
  have h := HLm_submod hΓ [F16] L6007 [F210]
  rw [show [F16] ++ L6007 ++ [F210] = L6006 from rfl, show [F16] ++ L6007 = L6003 from rfl,
    show L6007 ++ [F210] = L6004 from rfl] at h
  rw [i3429 hinj, i3427 hinj, i3428 hinj, i3430 hinj] at h
  linarith

theorem row1203 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6008 + (1 : ℝ) * HLm Γ 5 L6010 + (-1 : ℝ) * HLm Γ 5 L6012 + (-1 : ℝ) * HLm Γ 5 L6014 := by
  have h := HLm_submod hΓ [F210] L6015 [F96]
  rw [show [F210] ++ L6015 ++ [F96] = L6013 from rfl, show [F210] ++ L6015 = L6009 from rfl,
    show L6015 ++ [F96] = L6011 from rfl] at h
  rw [i3433 hinj, i3431 hinj, i3432 hinj, i3434 hinj] at h
  linarith

theorem row1204 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L6017 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5087 := by
  have h := HLm_submod hΓ [F10] L5088 [F210]
  rw [show [F10] ++ L5088 ++ [F210] = L6019 from rfl, show [F10] ++ L5088 = L6016 from rfl,
    show L5088 ++ [F210] = L6018 from rfl] at h
  rw [i3437 hinj, i3435 hinj, i3436 hinj, i2866 hinj] at h
  linarith

theorem row1205 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L5097 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5093 := by
  have h := HLm_submod hΓ [F10] L5094 [F210]
  rw [show [F10] ++ L5094 ++ [F210] = L6021 from rfl, show [F10] ++ L5094 = L6020 from rfl,
    show L5094 ++ [F210] = L5098 from rfl] at h
  rw [i3439 hinj, i3438 hinj, i2871 hinj, i2869 hinj] at h
  linarith

theorem row1206 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4725 + (1 : ℝ) * HLm Γ 5 L6023 + (-1 : ℝ) * HLm Γ 5 L6025 + (-1 : ℝ) * HLm Γ 5 L4723 := by
  have h := HLm_submod hΓ [F210] L6027 [F45]
  rw [show [F210] ++ L6027 ++ [F45] = L6026 from rfl, show [F210] ++ L6027 = L6022 from rfl,
    show L6027 ++ [F45] = L6024 from rfl] at h
  rw [i3442 hinj, i3440 hinj, i3441 hinj, i3443 hinj] at h
  linarith

theorem row1207 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4736 + (1 : ℝ) * HLm Γ 5 L6029 + (-1 : ℝ) * HLm Γ 5 L6031 + (-1 : ℝ) * HLm Γ 5 L4688 := by
  have h := HLm_submod hΓ [F9] L6033 [F211]
  rw [show [F9] ++ L6033 ++ [F211] = L6032 from rfl, show [F9] ++ L6033 = L6028 from rfl,
    show L6033 ++ [F211] = L6030 from rfl] at h
  rw [i3446 hinj, i3444 hinj, i3445 hinj, i3447 hinj] at h
  linarith

theorem row1208 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6034 + (1 : ℝ) * HLm Γ 5 L6036 + (-1 : ℝ) * HLm Γ 5 L6038 + (-1 : ℝ) * HLm Γ 5 L4693 := by
  have h := HLm_submod hΓ [F0] L6040 [F67]
  rw [show [F0] ++ L6040 ++ [F67] = L6039 from rfl, show [F0] ++ L6040 = L6035 from rfl,
    show L6040 ++ [F67] = L6037 from rfl] at h
  rw [i3450 hinj, i3448 hinj, i3449 hinj, i3451 hinj] at h
  linarith

theorem row1209 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L4701 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L4699 := by
  have h := HLm_submod hΓ [F10] L4700 [F210]
  rw [show [F10] ++ L4700 ++ [F210] = L6043 from rfl, show [F10] ++ L4700 = L6041 from rfl,
    show L4700 ++ [F210] = L6042 from rfl] at h
  rw [i3454 hinj, i3452 hinj, i3453 hinj, i2639 hinj] at h
  linarith

theorem row1210 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4558 + (1 : ℝ) * HLm Γ 5 L4709 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L4707 := by
  have h := HLm_submod hΓ [F7] L6047 [F67]
  rw [show [F7] ++ L6047 ++ [F67] = L6046 from rfl, show [F7] ++ L6047 = L6044 from rfl,
    show L6047 ++ [F67] = L6045 from rfl] at h
  rw [i3457 hinj, i3455 hinj, i3456 hinj, i3458 hinj] at h
  linarith

theorem row1211 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L4767 + (-1 : ℝ) * HLm Γ 5 L4558 + (-1 : ℝ) * HLm Γ 5 L4759 := by
  have h := HLm_submod hΓ [F0] L6051 [F217]
  rw [show [F0] ++ L6051 ++ [F217] = L6050 from rfl, show [F0] ++ L6051 = L6048 from rfl,
    show L6051 ++ [F217] = L6049 from rfl] at h
  rw [i3461 hinj, i3459 hinj, i3460 hinj, i3462 hinj] at h
  linarith

theorem row1212 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6052 + (1 : ℝ) * HLm Γ 5 L6054 + (-1 : ℝ) * HLm Γ 5 L5461 + (-1 : ℝ) * HLm Γ 5 L6057 := by
  have h := HLm_submod hΓ [F0] L6058 [F67]
  rw [show [F0] ++ L6058 ++ [F67] = L6056 from rfl, show [F0] ++ L6058 = L6053 from rfl,
    show L6058 ++ [F67] = L6055 from rfl] at h
  rw [i3465 hinj, i3463 hinj, i3464 hinj, i3466 hinj] at h
  linarith

theorem row1213 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6059 + (1 : ℝ) * HLm Γ 5 L4775 + (-1 : ℝ) * HLm Γ 5 L6062 + (-1 : ℝ) * HLm Γ 5 L4773 := by
  have h := HLm_submod hΓ [F51] L6064 [F210]
  rw [show [F51] ++ L6064 ++ [F210] = L6063 from rfl, show [F51] ++ L6064 = L6060 from rfl,
    show L6064 ++ [F210] = L6061 from rfl] at h
  rw [i3469 hinj, i3467 hinj, i3468 hinj, i3470 hinj] at h
  linarith

theorem row1214 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L6066 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L1537 := by
  have h := HLm_submod hΓ [F0] L6069 [F210]
  rw [show [F0] ++ L6069 ++ [F210] = L6068 from rfl, show [F0] ++ L6069 = L6065 from rfl,
    show L6069 ++ [F210] = L6067 from rfl] at h
  rw [i3473 hinj, i3471 hinj, i3472 hinj, i3474 hinj] at h
  linarith

theorem row1215 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L6071 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6074 := by
  have h := HLm_submod hΓ [F0] L6075 [F210]
  rw [show [F0] ++ L6075 ++ [F210] = L6073 from rfl, show [F0] ++ L6075 = L6070 from rfl,
    show L6075 ++ [F210] = L6072 from rfl] at h
  rw [i3477 hinj, i3475 hinj, i3476 hinj, i3478 hinj] at h
  linarith

theorem row1216 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5739 + (1 : ℝ) * HLm Γ 5 L6077 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6080 := by
  have h := HLm_submod hΓ [F0] L6081 [F4]
  rw [show [F0] ++ L6081 ++ [F4] = L6079 from rfl, show [F0] ++ L6081 = L6076 from rfl,
    show L6081 ++ [F4] = L6078 from rfl] at h
  rw [i3481 hinj, i3479 hinj, i3480 hinj, i3482 hinj] at h
  linarith

theorem row1217 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5739 + (1 : ℝ) * HLm Γ 5 L6082 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6080 := by
  have h := HLm_submod hΓ [F0] L6081 [F25]
  rw [show [F0] ++ L6081 ++ [F25] = L6084 from rfl, show [F0] ++ L6081 = L6076 from rfl,
    show L6081 ++ [F25] = L6083 from rfl] at h
  rw [i3484 hinj, i3479 hinj, i3483 hinj, i3482 hinj] at h
  linarith

theorem row1218 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5506 + (1 : ℝ) * HLm Γ 5 L4863 + (-1 : ℝ) * HLm Γ 5 L6087 + (-1 : ℝ) * HLm Γ 5 L4785 := by
  have h := HLm_submod hΓ [F0] L4786 [F2]
  rw [show [F0] ++ L4786 ++ [F2] = L6088 from rfl, show [F0] ++ L4786 = L6085 from rfl,
    show L4786 ++ [F2] = L6086 from rfl] at h
  rw [i3487 hinj, i3485 hinj, i3486 hinj, i2691 hinj] at h
  linarith

theorem row1219 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4441 + (1 : ℝ) * HLm Γ 5 L6089 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L4793 := by
  have h := HLm_submod hΓ [F0] L4794 [F4]
  rw [show [F0] ++ L4794 ++ [F4] = L6091 from rfl, show [F0] ++ L4794 = L4795 from rfl,
    show L4794 ++ [F4] = L6090 from rfl] at h
  rw [i3489 hinj, i2696 hinj, i3488 hinj, i2695 hinj] at h
  linarith

theorem row1220 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1420 + (1 : ℝ) * HLm Γ 5 L4807 + (-1 : ℝ) * HLm Γ 5 L5515 + (-1 : ℝ) * HLm Γ 5 L4805 := by
  have h := HLm_submod hΓ [F0] L4806 [F210]
  rw [show [F0] ++ L4806 ++ [F210] = L6094 from rfl, show [F0] ++ L4806 = L6092 from rfl,
    show L4806 ++ [F210] = L6093 from rfl] at h
  rw [i3492 hinj, i3490 hinj, i3491 hinj, i2702 hinj] at h
  linarith

theorem row1221 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6095 + (1 : ℝ) * HLm Γ 5 L5156 + (-1 : ℝ) * HLm Γ 5 L5489 + (-1 : ℝ) * HLm Γ 5 L3545 := by
  have h := HLm_submod hΓ [F0] L6099 [F2]
  rw [show [F0] ++ L6099 ++ [F2] = L6098 from rfl, show [F0] ++ L6099 = L6096 from rfl,
    show L6099 ++ [F2] = L6097 from rfl] at h
  rw [i3495 hinj, i3493 hinj, i3494 hinj, i3496 hinj] at h
  linarith

theorem row1222 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4818 + (1 : ℝ) * HLm Γ 5 L4826 + (-1 : ℝ) * HLm Γ 5 L5489 + (-1 : ℝ) * HLm Γ 5 L4824 := by
  have h := HLm_submod hΓ [F0] L6103 [F12]
  rw [show [F0] ++ L6103 ++ [F12] = L6102 from rfl, show [F0] ++ L6103 = L6100 from rfl,
    show L6103 ++ [F12] = L6101 from rfl] at h
  rw [i3499 hinj, i3497 hinj, i3498 hinj, i3500 hinj] at h
  linarith

theorem row1223 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6104 + (1 : ℝ) * HLm Γ 5 L6106 + (-1 : ℝ) * HLm Γ 5 L6108 + (-1 : ℝ) * HLm Γ 5 L1624 := by
  have h := HLm_submod hΓ [F111] L6110 [F210]
  rw [show [F111] ++ L6110 ++ [F210] = L6109 from rfl, show [F111] ++ L6110 = L6105 from rfl,
    show L6110 ++ [F210] = L6107 from rfl] at h
  rw [i3503 hinj, i3501 hinj, i3502 hinj, i3504 hinj] at h
  linarith

theorem row1224 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4455 + (1 : ℝ) * HLm Γ 5 L6112 + (-1 : ℝ) * HLm Γ 5 L5529 + (-1 : ℝ) * HLm Γ 5 L6115 := by
  have h := HLm_submod hΓ [F0] L6116 [F1]
  rw [show [F0] ++ L6116 ++ [F1] = L6114 from rfl, show [F0] ++ L6116 = L6111 from rfl,
    show L6116 ++ [F1] = L6113 from rfl] at h
  rw [i3507 hinj, i3505 hinj, i3506 hinj, i3508 hinj] at h
  linarith

theorem row1225 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4274 + (1 : ℝ) * HLm Γ 5 L6118 + (-1 : ℝ) * HLm Γ 5 L6120 + (-1 : ℝ) * HLm Γ 5 L6122 := by
  have h := HLm_submod hΓ [F0] L6123 [F217]
  rw [show [F0] ++ L6123 ++ [F217] = L6121 from rfl, show [F0] ++ L6123 = L6117 from rfl,
    show L6123 ++ [F217] = L6119 from rfl] at h
  rw [i3511 hinj, i3509 hinj, i3510 hinj, i3512 hinj] at h
  linarith

theorem row1226 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6124 + (1 : ℝ) * HLm Γ 5 L4849 + (-1 : ℝ) * HLm Γ 5 L6127 + (-1 : ℝ) * HLm Γ 5 L4847 := by
  have h := HLm_submod hΓ [F108] L6129 [F210]
  rw [show [F108] ++ L6129 ++ [F210] = L6128 from rfl, show [F108] ++ L6129 = L6125 from rfl,
    show L6129 ++ [F210] = L6126 from rfl] at h
  rw [i3515 hinj, i3513 hinj, i3514 hinj, i3516 hinj] at h
  linarith

theorem row1227 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2700 + (1 : ℝ) * HLm Γ 5 L6131 + (-1 : ℝ) * HLm Γ 5 L6133 + (-1 : ℝ) * HLm Γ 5 L6135 := by
  have h := HLm_submod hΓ [F0] L6136 [F210]
  rw [show [F0] ++ L6136 ++ [F210] = L6134 from rfl, show [F0] ++ L6136 = L6130 from rfl,
    show L6136 ++ [F210] = L6132 from rfl] at h
  rw [i3519 hinj, i3517 hinj, i3518 hinj, i3520 hinj] at h
  linarith

theorem row1228 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6137 + (1 : ℝ) * HLm Γ 5 L6139 + (-1 : ℝ) * HLm Γ 5 L6141 + (-1 : ℝ) * HLm Γ 5 L6143 := by
  have h := HLm_submod hΓ [F2] L6144 [F33]
  rw [show [F2] ++ L6144 ++ [F33] = L6142 from rfl, show [F2] ++ L6144 = L6138 from rfl,
    show L6144 ++ [F33] = L6140 from rfl] at h
  rw [i3523 hinj, i3521 hinj, i3522 hinj, i3524 hinj] at h
  linarith

theorem row1229 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4258 + (1 : ℝ) * HLm Γ 5 L4871 + (-1 : ℝ) * HLm Γ 5 L5524 + (-1 : ℝ) * HLm Γ 5 L4861 := by
  have h := HLm_submod hΓ [F0] L6148 [F55]
  rw [show [F0] ++ L6148 ++ [F55] = L6147 from rfl, show [F0] ++ L6148 = L6145 from rfl,
    show L6148 ++ [F55] = L6146 from rfl] at h
  rw [i3527 hinj, i3525 hinj, i3526 hinj, i3528 hinj] at h
  linarith

theorem row1230 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4842 + (1 : ℝ) * HLm Γ 5 L4871 + (-1 : ℝ) * HLm Γ 5 L5524 + (-1 : ℝ) * HLm Γ 5 L4867 := by
  have h := HLm_submod hΓ [F0] L6152 [F96]
  rw [show [F0] ++ L6152 ++ [F96] = L6151 from rfl, show [F0] ++ L6152 = L6149 from rfl,
    show L6152 ++ [F96] = L6150 from rfl] at h
  rw [i3531 hinj, i3529 hinj, i3530 hinj, i3532 hinj] at h
  linarith

theorem row1231 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6153 + (1 : ℝ) * HLm Γ 5 L6155 + (-1 : ℝ) * HLm Γ 5 L6157 + (-1 : ℝ) * HLm Γ 5 L6159 := by
  have h := HLm_submod hΓ [F1] L6160 [F34]
  rw [show [F1] ++ L6160 ++ [F34] = L6158 from rfl, show [F1] ++ L6160 = L6154 from rfl,
    show L6160 ++ [F34] = L6156 from rfl] at h
  rw [i3535 hinj, i3533 hinj, i3534 hinj, i3536 hinj] at h
  linarith

theorem row1232 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4877 + (1 : ℝ) * HLm Γ 5 L6161 + (-1 : ℝ) * HLm Γ 5 L6163 + (-1 : ℝ) * HLm Γ 5 L4875 := by
  have h := HLm_submod hΓ [F210] L4876 [F33]
  rw [show [F210] ++ L4876 ++ [F33] = L6164 from rfl, show [F210] ++ L4876 = L4878 from rfl,
    show L4876 ++ [F33] = L6162 from rfl] at h
  rw [i3538 hinj, i2745 hinj, i3537 hinj, i2744 hinj] at h
  linarith

theorem row1233 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6165 + (1 : ℝ) * HLm Γ 5 L4856 + (-1 : ℝ) * HLm Γ 5 L6168 + (-1 : ℝ) * HLm Γ 5 L6170 := by
  have h := HLm_submod hΓ [F0] L6171 [F82]
  rw [show [F0] ++ L6171 ++ [F82] = L6169 from rfl, show [F0] ++ L6171 = L6166 from rfl,
    show L6171 ++ [F82] = L6167 from rfl] at h
  rw [i3541 hinj, i3539 hinj, i3540 hinj, i3542 hinj] at h
  linarith

theorem row1234 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4895 + (1 : ℝ) * HLm Γ 5 L6172 + (-1 : ℝ) * HLm Γ 5 L6174 + (-1 : ℝ) * HLm Γ 5 L4893 := by
  have h := HLm_submod hΓ [F1] L4894 [F16]
  rw [show [F1] ++ L4894 ++ [F16] = L6175 from rfl, show [F1] ++ L4894 = L4896 from rfl,
    show L4894 ++ [F16] = L6173 from rfl] at h
  rw [i3544 hinj, i2756 hinj, i3543 hinj, i2755 hinj] at h
  linarith

theorem row1235 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6176 + (1 : ℝ) * HLm Γ 5 L4919 + (-1 : ℝ) * HLm Γ 5 L6179 + (-1 : ℝ) * HLm Γ 5 L4915 := by
  have h := HLm_submod hΓ [F0] L6181 [F43]
  rw [show [F0] ++ L6181 ++ [F43] = L6180 from rfl, show [F0] ++ L6181 = L6177 from rfl,
    show L6181 ++ [F43] = L6178 from rfl] at h
  rw [i3547 hinj, i3545 hinj, i3546 hinj, i3548 hinj] at h
  linarith

theorem row1236 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4902 + (1 : ℝ) * HLm Γ 5 L4932 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L4900 := by
  have h := HLm_submod hΓ [F0] L6185 [F4]
  rw [show [F0] ++ L6185 ++ [F4] = L6184 from rfl, show [F0] ++ L6185 = L6182 from rfl,
    show L6185 ++ [F4] = L6183 from rfl] at h
  rw [i3551 hinj, i3549 hinj, i3550 hinj, i3552 hinj] at h
  linarith

theorem row1237 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4522 + (1 : ℝ) * HLm Γ 5 L6187 + (-1 : ℝ) * HLm Γ 5 L5668 + (-1 : ℝ) * HLm Γ 5 L4906 := by
  have h := HLm_submod hΓ [F0] L6190 [F1]
  rw [show [F0] ++ L6190 ++ [F1] = L6189 from rfl, show [F0] ++ L6190 = L6186 from rfl,
    show L6190 ++ [F1] = L6188 from rfl] at h
  rw [i3555 hinj, i3553 hinj, i3554 hinj, i3556 hinj] at h
  linarith

theorem row1238 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6191 + (1 : ℝ) * HLm Γ 5 L6193 + (-1 : ℝ) * HLm Γ 5 L6195 + (-1 : ℝ) * HLm Γ 5 L4917 := by
  have h := HLm_submod hΓ [F51] L4918 [F210]
  rw [show [F51] ++ L4918 ++ [F210] = L6196 from rfl, show [F51] ++ L4918 = L6192 from rfl,
    show L4918 ++ [F210] = L6194 from rfl] at h
  rw [i3559 hinj, i3557 hinj, i3558 hinj, i2770 hinj] at h
  linarith

theorem row1239 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4927 + (1 : ℝ) * HLm Γ 5 L6089 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L4925 := by
  have h := HLm_submod hΓ [F0] L6200 [F4]
  rw [show [F0] ++ L6200 ++ [F4] = L6199 from rfl, show [F0] ++ L6200 = L6197 from rfl,
    show L6200 ++ [F4] = L6198 from rfl] at h
  rw [i3562 hinj, i3560 hinj, i3561 hinj, i3563 hinj] at h
  linarith

theorem row1240 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L5819 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L1871 := by
  have h := HLm_submod hΓ [F1] L6204 [F210]
  rw [show [F1] ++ L6204 ++ [F210] = L6203 from rfl, show [F1] ++ L6204 = L6201 from rfl,
    show L6204 ++ [F210] = L6202 from rfl] at h
  rw [i3566 hinj, i3564 hinj, i3565 hinj, i3567 hinj] at h
  linarith

theorem row1241 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6205 + (1 : ℝ) * HLm Γ 5 L6207 + (-1 : ℝ) * HLm Γ 5 L6209 + (-1 : ℝ) * HLm Γ 5 L1155 := by
  have h := HLm_submod hΓ [F210] L6211 [F36]
  rw [show [F210] ++ L6211 ++ [F36] = L6210 from rfl, show [F210] ++ L6211 = L6206 from rfl,
    show L6211 ++ [F36] = L6208 from rfl] at h
  rw [i3570 hinj, i3568 hinj, i3569 hinj, i3571 hinj] at h
  linarith

theorem row1242 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L4955 + (-1 : ℝ) * HLm Γ 5 L4558 + (-1 : ℝ) * HLm Γ 5 L4952 := by
  have h := HLm_submod hΓ [F0] L6215 [F219]
  rw [show [F0] ++ L6215 ++ [F219] = L6214 from rfl, show [F0] ++ L6215 = L6212 from rfl,
    show L6215 ++ [F219] = L6213 from rfl] at h
  rw [i3574 hinj, i3572 hinj, i3573 hinj, i3575 hinj] at h
  linarith

theorem row1243 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6216 + (1 : ℝ) * HLm Γ 5 L4962 + (-1 : ℝ) * HLm Γ 5 L6219 + (-1 : ℝ) * HLm Γ 5 L4960 := by
  have h := HLm_submod hΓ [F47] L4961 [F210]
  rw [show [F47] ++ L4961 ++ [F210] = L6220 from rfl, show [F47] ++ L4961 = L6217 from rfl,
    show L4961 ++ [F210] = L6218 from rfl] at h
  rw [i3578 hinj, i3576 hinj, i3577 hinj, i2797 hinj] at h
  linarith

theorem row1244 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4400 + (1 : ℝ) * HLm Γ 5 L4970 + (-1 : ℝ) * HLm Γ 5 L6223 + (-1 : ℝ) * HLm Γ 5 L4968 := by
  have h := HLm_submod hΓ [F7] L6225 [F67]
  rw [show [F7] ++ L6225 ++ [F67] = L6224 from rfl, show [F7] ++ L6225 = L6221 from rfl,
    show L6225 ++ [F67] = L6222 from rfl] at h
  rw [i3581 hinj, i3579 hinj, i3580 hinj, i3582 hinj] at h
  linarith

theorem row1245 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6226 + (1 : ℝ) * HLm Γ 5 L4984 + (-1 : ℝ) * HLm Γ 5 L5719 + (-1 : ℝ) * HLm Γ 5 L4982 := by
  have h := HLm_submod hΓ [F1] L6230 [F7]
  rw [show [F1] ++ L6230 ++ [F7] = L6229 from rfl, show [F1] ++ L6230 = L6227 from rfl,
    show L6230 ++ [F7] = L6228 from rfl] at h
  rw [i3585 hinj, i3583 hinj, i3584 hinj, i3586 hinj] at h
  linarith

theorem row1246 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4995 + (1 : ℝ) * HLm Γ 5 L6231 + (-1 : ℝ) * HLm Γ 5 L6233 + (-1 : ℝ) * HLm Γ 5 L4993 := by
  have h := HLm_submod hΓ [F210] L4994 [F30]
  rw [show [F210] ++ L4994 ++ [F30] = L6234 from rfl, show [F210] ++ L4994 = L4996 from rfl,
    show L4994 ++ [F30] = L6232 from rfl] at h
  rw [i3588 hinj, i2816 hinj, i3587 hinj, i2815 hinj] at h
  linarith

theorem row1247 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6235 + (1 : ℝ) * HLm Γ 5 L5002 + (-1 : ℝ) * HLm Γ 5 L6238 + (-1 : ℝ) * HLm Γ 5 L5000 := by
  have h := HLm_submod hΓ [F16] L6240 [F210]
  rw [show [F16] ++ L6240 ++ [F210] = L6239 from rfl, show [F16] ++ L6240 = L6236 from rfl,
    show L6240 ++ [F210] = L6237 from rfl] at h
  rw [i3591 hinj, i3589 hinj, i3590 hinj, i3592 hinj] at h
  linarith

theorem row1248 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5008 + (1 : ℝ) * HLm Γ 5 L6242 + (-1 : ℝ) * HLm Γ 5 L6244 + (-1 : ℝ) * HLm Γ 5 L5006 := by
  have h := HLm_submod hΓ [F67] L6246 [F36]
  rw [show [F67] ++ L6246 ++ [F36] = L6245 from rfl, show [F67] ++ L6246 = L6241 from rfl,
    show L6246 ++ [F36] = L6243 from rfl] at h
  rw [i3595 hinj, i3593 hinj, i3594 hinj, i3596 hinj] at h
  linarith

theorem row1249 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4558 + (1 : ℝ) * HLm Γ 5 L5016 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5014 := by
  have h := HLm_submod hΓ [F51] L6250 [F67]
  rw [show [F51] ++ L6250 ++ [F67] = L6249 from rfl, show [F51] ++ L6250 = L6247 from rfl,
    show L6250 ++ [F67] = L6248 from rfl] at h
  rw [i3599 hinj, i3597 hinj, i3598 hinj, i3600 hinj] at h
  linarith

theorem row1250 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1614 + (1 : ℝ) * HLm Γ 5 L5284 + (-1 : ℝ) * HLm Γ 5 L5529 + (-1 : ℝ) * HLm Γ 5 L5281 := by
  have h := HLm_submod hΓ [F0] L5282 [F210]
  rw [show [F0] ++ L5282 ++ [F210] = L6252 from rfl, show [F0] ++ L5282 = L6251 from rfl,
    show L5282 ++ [F210] = L5285 from rfl] at h
  rw [i3602 hinj, i3601 hinj, i2980 hinj, i2978 hinj] at h
  linarith

theorem row1251 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6253 + (1 : ℝ) * HLm Γ 5 L6255 + (-1 : ℝ) * HLm Γ 5 L6257 + (-1 : ℝ) * HLm Γ 5 L6259 := by
  have h := HLm_submod hΓ [F0] L6260 [F210]
  rw [show [F0] ++ L6260 ++ [F210] = L6258 from rfl, show [F0] ++ L6260 = L6254 from rfl,
    show L6260 ++ [F210] = L6256 from rfl] at h
  rw [i3605 hinj, i3603 hinj, i3604 hinj, i3606 hinj] at h
  linarith

theorem row1252 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5927 + (1 : ℝ) * HLm Γ 5 L6262 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6265 := by
  have h := HLm_submod hΓ [F1] L6266 [F17]
  rw [show [F1] ++ L6266 ++ [F17] = L6264 from rfl, show [F1] ++ L6266 = L6261 from rfl,
    show L6266 ++ [F17] = L6263 from rfl] at h
  rw [i3609 hinj, i3607 hinj, i3608 hinj, i3610 hinj] at h
  linarith

theorem row1253 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1307 + (1 : ℝ) * HLm Γ 5 L6268 + (-1 : ℝ) * HLm Γ 5 L6270 + (-1 : ℝ) * HLm Γ 5 L5020 := by
  have h := HLm_submod hΓ [F0] L6272 [F228]
  rw [show [F0] ++ L6272 ++ [F228] = L6271 from rfl, show [F0] ++ L6272 = L6267 from rfl,
    show L6272 ++ [F228] = L6269 from rfl] at h
  rw [i3613 hinj, i3611 hinj, i3612 hinj, i3614 hinj] at h
  linarith

theorem row1254 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5927 + (1 : ℝ) * HLm Γ 5 L6274 + (-1 : ℝ) * HLm Γ 5 L5931 + (-1 : ℝ) * HLm Γ 5 L5022 := by
  have h := HLm_submod hΓ [F1] L5023 [F7]
  rw [show [F1] ++ L5023 ++ [F7] = L6276 from rfl, show [F1] ++ L5023 = L6273 from rfl,
    show L5023 ++ [F7] = L6275 from rfl] at h
  rw [i3617 hinj, i3615 hinj, i3616 hinj, i2829 hinj] at h
  linarith

theorem row1255 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5927 + (1 : ℝ) * HLm Γ 5 L5024 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5022 := by
  have h := HLm_submod hΓ [F1] L5023 [F17]
  rw [show [F1] ++ L5023 ++ [F17] = L6278 from rfl, show [F1] ++ L5023 = L6273 from rfl,
    show L5023 ++ [F17] = L6277 from rfl] at h
  rw [i3619 hinj, i3615 hinj, i3618 hinj, i2829 hinj] at h
  linarith

theorem row1256 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5927 + (1 : ℝ) * HLm Γ 5 L5062 + (-1 : ℝ) * HLm Γ 5 L6089 + (-1 : ℝ) * HLm Γ 5 L5060 := by
  have h := HLm_submod hΓ [F1] L6282 [F9]
  rw [show [F1] ++ L6282 ++ [F9] = L6281 from rfl, show [F1] ++ L6282 = L6279 from rfl,
    show L6282 ++ [F9] = L6280 from rfl] at h
  rw [i3622 hinj, i3620 hinj, i3621 hinj, i3623 hinj] at h
  linarith

theorem row1257 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5038 + (1 : ℝ) * HLm Γ 5 L6283 + (-1 : ℝ) * HLm Γ 5 L6285 + (-1 : ℝ) * HLm Γ 5 L5036 := by
  have h := HLm_submod hΓ [F210] L5037 [F85]
  rw [show [F210] ++ L5037 ++ [F85] = L6286 from rfl, show [F210] ++ L5037 = L5039 from rfl,
    show L5037 ++ [F85] = L6284 from rfl] at h
  rw [i3625 hinj, i2837 hinj, i3624 hinj, i2836 hinj] at h
  linarith

theorem row1258 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5271 + (1 : ℝ) * HLm Γ 5 L6288 + (-1 : ℝ) * HLm Γ 5 L6290 + (-1 : ℝ) * HLm Γ 5 L5268 := by
  have h := HLm_submod hΓ [F210] L5269 [F85]
  rw [show [F210] ++ L5269 ++ [F85] = L6291 from rfl, show [F210] ++ L5269 = L6287 from rfl,
    show L5269 ++ [F85] = L6289 from rfl] at h
  rw [i3628 hinj, i3626 hinj, i3627 hinj, i2971 hinj] at h
  linarith

theorem row1259 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5046 + (1 : ℝ) * HLm Γ 5 L6292 + (-1 : ℝ) * HLm Γ 5 L6294 + (-1 : ℝ) * HLm Γ 5 L5044 := by
  have h := HLm_submod hΓ [F210] L5045 [F36]
  rw [show [F210] ++ L5045 ++ [F36] = L6295 from rfl, show [F210] ++ L5045 = L5047 from rfl,
    show L5045 ++ [F36] = L6293 from rfl] at h
  rw [i3630 hinj, i2841 hinj, i3629 hinj, i2840 hinj] at h
  linarith

theorem row1260 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6296 + (1 : ℝ) * HLm Γ 5 L6298 + (-1 : ℝ) * HLm Γ 5 L6300 + (-1 : ℝ) * HLm Γ 5 L5049 := by
  have h := HLm_submod hΓ [F1] L6302 [F62]
  rw [show [F1] ++ L6302 ++ [F62] = L6301 from rfl, show [F1] ++ L6302 = L6297 from rfl,
    show L6302 ++ [F62] = L6299 from rfl] at h
  rw [i3633 hinj, i3631 hinj, i3632 hinj, i3634 hinj] at h
  linarith

theorem row1261 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6303 + (1 : ℝ) * HLm Γ 5 L5076 + (-1 : ℝ) * HLm Γ 5 L6306 + (-1 : ℝ) * HLm Γ 5 L5072 := by
  have h := HLm_submod hΓ [F51] L6308 [F210]
  rw [show [F51] ++ L6308 ++ [F210] = L6307 from rfl, show [F51] ++ L6308 = L6304 from rfl,
    show L6308 ++ [F210] = L6305 from rfl] at h
  rw [i3637 hinj, i3635 hinj, i3636 hinj, i3638 hinj] at h
  linarith

theorem row1262 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1701 + (1 : ℝ) * HLm Γ 5 L5302 + (-1 : ℝ) * HLm Γ 5 L6310 + (-1 : ℝ) * HLm Γ 5 L5298 := by
  have h := HLm_submod hΓ [F7] L5299 [F210]
  rw [show [F7] ++ L5299 ++ [F210] = L6311 from rfl, show [F7] ++ L5299 = L6309 from rfl,
    show L5299 ++ [F210] = L5303 from rfl] at h
  rw [i3640 hinj, i3639 hinj, i2990 hinj, i2988 hinj] at h
  linarith

theorem row1263 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6312 + (1 : ℝ) * HLm Γ 5 L5181 + (-1 : ℝ) * HLm Γ 5 L6315 + (-1 : ℝ) * HLm Γ 5 L5177 := by
  have h := HLm_submod hΓ [F9] L6317 [F210]
  rw [show [F9] ++ L6317 ++ [F210] = L6316 from rfl, show [F9] ++ L6317 = L6313 from rfl,
    show L6317 ++ [F210] = L6314 from rfl] at h
  rw [i3643 hinj, i3641 hinj, i3642 hinj, i3644 hinj] at h
  linarith

theorem row1264 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5108 + (1 : ℝ) * HLm Γ 5 L5091 + (-1 : ℝ) * HLm Γ 5 L6320 + (-1 : ℝ) * HLm Γ 5 L5089 := by
  have h := HLm_submod hΓ [F7] L5090 [F47]
  rw [show [F7] ++ L5090 ++ [F47] = L6321 from rfl, show [F7] ++ L5090 = L6318 from rfl,
    show L5090 ++ [F47] = L6319 from rfl] at h
  rw [i3647 hinj, i3645 hinj, i3646 hinj, i2867 hinj] at h
  linarith

theorem row1265 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6322 + (1 : ℝ) * HLm Γ 5 L6324 + (-1 : ℝ) * HLm Γ 5 L6326 + (-1 : ℝ) * HLm Γ 5 L6328 := by
  have h := HLm_submod hΓ [F9] L6329 [F62]
  rw [show [F9] ++ L6329 ++ [F62] = L6327 from rfl, show [F9] ++ L6329 = L6323 from rfl,
    show L6329 ++ [F62] = L6325 from rfl] at h
  rw [i3650 hinj, i3648 hinj, i3649 hinj, i3651 hinj] at h
  linarith

theorem row1266 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5259 + (1 : ℝ) * HLm Γ 5 L6331 + (-1 : ℝ) * HLm Γ 5 L6333 + (-1 : ℝ) * HLm Γ 5 L5255 := by
  have h := HLm_submod hΓ [F210] L5256 [F17]
  rw [show [F210] ++ L5256 ++ [F17] = L6334 from rfl, show [F210] ++ L5256 = L6330 from rfl,
    show L5256 ++ [F17] = L6332 from rfl] at h
  rw [i3654 hinj, i3652 hinj, i3653 hinj, i2964 hinj] at h
  linarith

theorem row1267 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6335 + (1 : ℝ) * HLm Γ 5 L5363 + (-1 : ℝ) * HLm Γ 5 L6338 + (-1 : ℝ) * HLm Γ 5 L5360 := by
  have h := HLm_submod hΓ [F108] L6340 [F210]
  rw [show [F108] ++ L6340 ++ [F210] = L6339 from rfl, show [F108] ++ L6340 = L6336 from rfl,
    show L6340 ++ [F210] = L6337 from rfl] at h
  rw [i3657 hinj, i3655 hinj, i3656 hinj, i3658 hinj] at h
  linarith

theorem row1268 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5922 + (1 : ℝ) * HLm Γ 5 L5146 + (-1 : ℝ) * HLm Γ 5 L5639 + (-1 : ℝ) * HLm Γ 5 L3820 := by
  have h := HLm_submod hΓ [F1] L5127 [F7]
  rw [show [F1] ++ L5127 ++ [F7] = L6343 from rfl, show [F1] ++ L5127 = L6341 from rfl,
    show L5127 ++ [F7] = L6342 from rfl] at h
  rw [i3661 hinj, i3659 hinj, i3660 hinj, i2887 hinj] at h
  linarith

theorem row1269 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6344 + (1 : ℝ) * HLm Γ 5 L5136 + (-1 : ℝ) * HLm Γ 5 L6347 + (-1 : ℝ) * HLm Γ 5 L5134 := by
  have h := HLm_submod hΓ [F46] L6349 [F210]
  rw [show [F46] ++ L6349 ++ [F210] = L6348 from rfl, show [F46] ++ L6349 = L6345 from rfl,
    show L6349 ++ [F210] = L6346 from rfl] at h
  rw [i3664 hinj, i3662 hinj, i3663 hinj, i3665 hinj] at h
  linarith

theorem row1270 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5164 + (1 : ℝ) * HLm Γ 5 L5700 + (-1 : ℝ) * HLm Γ 5 L6352 + (-1 : ℝ) * HLm Γ 5 L5162 := by
  have h := HLm_submod hΓ [F0] L6354 [F7]
  rw [show [F0] ++ L6354 ++ [F7] = L6353 from rfl, show [F0] ++ L6354 = L6350 from rfl,
    show L6354 ++ [F7] = L6351 from rfl] at h
  rw [i3668 hinj, i3666 hinj, i3667 hinj, i3669 hinj] at h
  linarith

theorem row1271 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5188 + (1 : ℝ) * HLm Γ 5 L6356 + (-1 : ℝ) * HLm Γ 5 L5931 + (-1 : ℝ) * HLm Γ 5 L5186 := by
  have h := HLm_submod hΓ [F1] L6359 [F2]
  rw [show [F1] ++ L6359 ++ [F2] = L6358 from rfl, show [F1] ++ L6359 = L6355 from rfl,
    show L6359 ++ [F2] = L6357 from rfl] at h
  rw [i3672 hinj, i3670 hinj, i3671 hinj, i3673 hinj] at h
  linarith

theorem row1272 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6360 + (1 : ℝ) * HLm Γ 5 L6362 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5203 := by
  have h := HLm_submod hΓ [F0] L5204 [F4]
  rw [show [F0] ++ L5204 ++ [F4] = L6364 from rfl, show [F0] ++ L5204 = L6361 from rfl,
    show L5204 ++ [F4] = L6363 from rfl] at h
  rw [i3676 hinj, i3674 hinj, i3675 hinj, i2933 hinj] at h
  linarith

theorem row1273 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6365 + (1 : ℝ) * HLm Γ 5 L5296 + (-1 : ℝ) * HLm Γ 5 L6368 + (-1 : ℝ) * HLm Γ 5 L5294 := by
  have h := HLm_submod hΓ [F107] L6370 [F210]
  rw [show [F107] ++ L6370 ++ [F210] = L6369 from rfl, show [F107] ++ L6370 = L6366 from rfl,
    show L6370 ++ [F210] = L6367 from rfl] at h
  rw [i3679 hinj, i3677 hinj, i3678 hinj, i3680 hinj] at h
  linarith

theorem row1274 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6371 + (1 : ℝ) * HLm Γ 5 L6373 + (-1 : ℝ) * HLm Γ 5 L6375 + (-1 : ℝ) * HLm Γ 5 L6377 := by
  have h := HLm_submod hΓ [F12] L6378 [F210]
  rw [show [F12] ++ L6378 ++ [F210] = L6376 from rfl, show [F12] ++ L6378 = L6372 from rfl,
    show L6378 ++ [F210] = L6374 from rfl] at h
  rw [i3683 hinj, i3681 hinj, i3682 hinj, i3684 hinj] at h
  linarith

theorem row1275 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4429 + (1 : ℝ) * HLm Γ 5 L5316 + (-1 : ℝ) * HLm Γ 5 L6381 + (-1 : ℝ) * HLm Γ 5 L5314 := by
  have h := HLm_submod hΓ [F0] L6383 [F1]
  rw [show [F0] ++ L6383 ++ [F1] = L6382 from rfl, show [F0] ++ L6383 = L6379 from rfl,
    show L6383 ++ [F1] = L6380 from rfl] at h
  rw [i3687 hinj, i3685 hinj, i3686 hinj, i3688 hinj] at h
  linarith

theorem row1276 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5343 + (1 : ℝ) * HLm Γ 5 L6384 + (-1 : ℝ) * HLm Γ 5 L6320 + (-1 : ℝ) * HLm Γ 5 L5341 := by
  have h := HLm_submod hΓ [F7] L5342 [F2]
  rw [show [F7] ++ L5342 ++ [F2] = L6386 from rfl, show [F7] ++ L5342 = L5344 from rfl,
    show L5342 ++ [F2] = L6385 from rfl] at h
  rw [i3690 hinj, i3013 hinj, i3689 hinj, i3012 hinj] at h
  linarith

theorem row1277 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6387 + (1 : ℝ) * HLm Γ 5 L6352 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6391 := by
  have h := HLm_submod hΓ [F2] L6392 [F7]
  rw [show [F2] ++ L6392 ++ [F7] = L6390 from rfl, show [F2] ++ L6392 = L6388 from rfl,
    show L6392 ++ [F7] = L6389 from rfl] at h
  rw [i3693 hinj, i3691 hinj, i3692 hinj, i3694 hinj] at h
  linarith

theorem row1278 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L5375 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5373 := by
  have h := HLm_submod hΓ [F7] L5374 [F210]
  rw [show [F7] ++ L5374 ++ [F210] = L6395 from rfl, show [F7] ++ L5374 = L6393 from rfl,
    show L5374 ++ [F210] = L6394 from rfl] at h
  rw [i3697 hinj, i3695 hinj, i3696 hinj, i3031 hinj] at h
  linarith

theorem row1279 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L6396 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L1694 := by
  have h := HLm_submod hΓ [F1] L2759 [F210]
  rw [show [F1] ++ L2759 ++ [F210] = L6398 from rfl, show [F1] ++ L2759 = L2760 from rfl,
    show L2759 ++ [F210] = L6397 from rfl] at h
  rw [i3699 hinj, i1560 hinj, i3698 hinj, i1559 hinj] at h
  linarith

theorem row1280 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L5394 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5391 := by
  have h := HLm_submod hΓ [F1] L6402 [F210]
  rw [show [F1] ++ L6402 ++ [F210] = L6401 from rfl, show [F1] ++ L6402 = L6399 from rfl,
    show L6402 ++ [F210] = L6400 from rfl] at h
  rw [i3702 hinj, i3700 hinj, i3701 hinj, i3703 hinj] at h
  linarith

theorem row1281 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5381 + (1 : ℝ) * HLm Γ 5 L6403 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5386 := by
  have h := HLm_submod hΓ [F1] L5387 [F16]
  rw [show [F1] ++ L5387 ++ [F16] = L6405 from rfl, show [F1] ++ L5387 = L5388 from rfl,
    show L5387 ++ [F16] = L6404 from rfl] at h
  rw [i3705 hinj, i3040 hinj, i3704 hinj, i3039 hinj] at h
  linarith

theorem row1282 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L6407 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6410 := by
  have h := HLm_submod hΓ [F1] L6411 [F210]
  rw [show [F1] ++ L6411 ++ [F210] = L6409 from rfl, show [F1] ++ L6411 = L6406 from rfl,
    show L6411 ++ [F210] = L6408 from rfl] at h
  rw [i3708 hinj, i3706 hinj, i3707 hinj, i3709 hinj] at h
  linarith

theorem row1283 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4558 + (1 : ℝ) * HLm Γ 5 L6412 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5403 := by
  have h := HLm_submod hΓ [F1] L5404 [F67]
  rw [show [F1] ++ L5404 ++ [F67] = L6414 from rfl, show [F1] ++ L5404 = L5405 from rfl,
    show L5404 ++ [F67] = L6413 from rfl] at h
  rw [i3711 hinj, i3051 hinj, i3710 hinj, i3050 hinj] at h
  linarith

theorem row1284 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L6416 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L1307 := by
  have h := HLm_submod hΓ [F1] L6419 [F210]
  rw [show [F1] ++ L6419 ++ [F210] = L6418 from rfl, show [F1] ++ L6419 = L6415 from rfl,
    show L6419 ++ [F210] = L6417 from rfl] at h
  rw [i3714 hinj, i3712 hinj, i3713 hinj, i3715 hinj] at h
  linarith

theorem row1285 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L5423 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5420 := by
  have h := HLm_submod hΓ [F1] L6423 [F210]
  rw [show [F1] ++ L6423 ++ [F210] = L6422 from rfl, show [F1] ++ L6423 = L6420 from rfl,
    show L6423 ++ [F210] = L6421 from rfl] at h
  rw [i3718 hinj, i3716 hinj, i3717 hinj, i3719 hinj] at h
  linarith

theorem row1286 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L5483 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5480 := by
  have h := HLm_submod hΓ [F1] L6427 [F210]
  rw [show [F1] ++ L6427 ++ [F210] = L6426 from rfl, show [F1] ++ L6427 = L6424 from rfl,
    show L6427 ++ [F210] = L6425 from rfl] at h
  rw [i3722 hinj, i3720 hinj, i3721 hinj, i3723 hinj] at h
  linarith

theorem row1287 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L5442 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5440 := by
  have h := HLm_submod hΓ [F1] L5441 [F210]
  rw [show [F1] ++ L5441 ++ [F210] = L6430 from rfl, show [F1] ++ L5441 = L6428 from rfl,
    show L5441 ++ [F210] = L6429 from rfl] at h
  rw [i3726 hinj, i3724 hinj, i3725 hinj, i3072 hinj] at h
  linarith

theorem row1288 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5502 + (1 : ℝ) * HLm Γ 5 L5751 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6434 := by
  have h := HLm_submod hΓ [F1] L6435 [F7]
  rw [show [F1] ++ L6435 ++ [F7] = L6433 from rfl, show [F1] ++ L6435 = L6431 from rfl,
    show L6435 ++ [F7] = L6432 from rfl] at h
  rw [i3729 hinj, i3727 hinj, i3728 hinj, i3730 hinj] at h
  linarith

theorem row1289 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L5448 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5446 := by
  have h := HLm_submod hΓ [F1] L5447 [F210]
  rw [show [F1] ++ L5447 ++ [F210] = L6438 from rfl, show [F1] ++ L5447 = L6436 from rfl,
    show L5447 ++ [F210] = L6437 from rfl] at h
  rw [i3733 hinj, i3731 hinj, i3732 hinj, i3075 hinj] at h
  linarith

theorem row1290 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L5455 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5453 := by
  have h := HLm_submod hΓ [F1] L5454 [F210]
  rw [show [F1] ++ L5454 ++ [F210] = L6441 from rfl, show [F1] ++ L5454 = L6439 from rfl,
    show L5454 ++ [F210] = L6440 from rfl] at h
  rw [i3736 hinj, i3734 hinj, i3735 hinj, i3079 hinj] at h
  linarith

theorem row1291 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L6257 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6253 := by
  have h := HLm_submod hΓ [F1] L6254 [F210]
  rw [show [F1] ++ L6254 ++ [F210] = L6443 from rfl, show [F1] ++ L6254 = L6442 from rfl,
    show L6254 ++ [F210] = L6258 from rfl] at h
  rw [i3738 hinj, i3737 hinj, i3605 hinj, i3603 hinj] at h
  linarith

theorem row1292 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4252 + (1 : ℝ) * HLm Γ 5 L5730 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6447 := by
  have h := HLm_submod hΓ [F1] L6448 [F7]
  rw [show [F1] ++ L6448 ++ [F7] = L6446 from rfl, show [F1] ++ L6448 = L6444 from rfl,
    show L6448 ++ [F7] = L6445 from rfl] at h
  rw [i3741 hinj, i3739 hinj, i3740 hinj, i3742 hinj] at h
  linarith

theorem row1293 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L5543 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5540 := by
  have h := HLm_submod hΓ [F1] L6452 [F210]
  rw [show [F1] ++ L6452 ++ [F210] = L6451 from rfl, show [F1] ++ L6452 = L6449 from rfl,
    show L6452 ++ [F210] = L6450 from rfl] at h
  rw [i3745 hinj, i3743 hinj, i3744 hinj, i3746 hinj] at h
  linarith

theorem row1294 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L5476 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5474 := by
  have h := HLm_submod hΓ [F1] L6456 [F210]
  rw [show [F1] ++ L6456 ++ [F210] = L6455 from rfl, show [F1] ++ L6456 = L6453 from rfl,
    show L6456 ++ [F210] = L6454 from rfl] at h
  rw [i3749 hinj, i3747 hinj, i3748 hinj, i3750 hinj] at h
  linarith

theorem row1295 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L5555 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5551 := by
  have h := HLm_submod hΓ [F1] L6460 [F210]
  rw [show [F1] ++ L6460 ++ [F210] = L6459 from rfl, show [F1] ++ L6460 = L6457 from rfl,
    show L6460 ++ [F210] = L6458 from rfl] at h
  rw [i3753 hinj, i3751 hinj, i3752 hinj, i3754 hinj] at h
  linarith

theorem row1296 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5502 + (1 : ℝ) * HLm Γ 5 L6462 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5500 := by
  have h := HLm_submod hΓ [F1] L6465 [F7]
  rw [show [F1] ++ L6465 ++ [F7] = L6464 from rfl, show [F1] ++ L6465 = L6461 from rfl,
    show L6465 ++ [F7] = L6463 from rfl] at h
  rw [i3757 hinj, i3755 hinj, i3756 hinj, i3758 hinj] at h
  linarith

theorem row1297 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5502 + (1 : ℝ) * HLm Γ 5 L5524 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6469 := by
  have h := HLm_submod hΓ [F1] L6470 [F7]
  rw [show [F1] ++ L6470 ++ [F7] = L6468 from rfl, show [F1] ++ L6470 = L6466 from rfl,
    show L6470 ++ [F7] = L6467 from rfl] at h
  rw [i3761 hinj, i3759 hinj, i3760 hinj, i3762 hinj] at h
  linarith

theorem row1298 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4252 + (1 : ℝ) * HLm Γ 5 L5536 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5534 := by
  have h := HLm_submod hΓ [F1] L6474 [F7]
  rw [show [F1] ++ L6474 ++ [F7] = L6473 from rfl, show [F1] ++ L6474 = L6471 from rfl,
    show L6474 ++ [F7] = L6472 from rfl] at h
  rw [i3765 hinj, i3763 hinj, i3764 hinj, i3766 hinj] at h
  linarith

theorem row1299 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5502 + (1 : ℝ) * HLm Γ 5 L5783 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5559 := by
  have h := HLm_submod hΓ [F1] L6478 [F7]
  rw [show [F1] ++ L6478 ++ [F7] = L6477 from rfl, show [F1] ++ L6478 = L6475 from rfl,
    show L6478 ++ [F7] = L6476 from rfl] at h
  rw [i3769 hinj, i3767 hinj, i3768 hinj, i3770 hinj] at h
  linarith

theorem row1300 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4252 + (1 : ℝ) * HLm Γ 5 L6480 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6483 := by
  have h := HLm_submod hΓ [F1] L6484 [F7]
  rw [show [F1] ++ L6484 ++ [F7] = L6482 from rfl, show [F1] ++ L6484 = L6479 from rfl,
    show L6484 ++ [F7] = L6481 from rfl] at h
  rw [i3773 hinj, i3771 hinj, i3772 hinj, i3774 hinj] at h
  linarith

theorem row1301 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L5576 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5574 := by
  have h := HLm_submod hΓ [F1] L6488 [F210]
  rw [show [F1] ++ L6488 ++ [F210] = L6487 from rfl, show [F1] ++ L6488 = L6485 from rfl,
    show L6488 ++ [F210] = L6486 from rfl] at h
  rw [i3777 hinj, i3775 hinj, i3776 hinj, i3778 hinj] at h
  linarith

theorem row1302 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4252 + (1 : ℝ) * HLm Γ 5 L5581 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5579 := by
  have h := HLm_submod hΓ [F1] L6492 [F7]
  rw [show [F1] ++ L6492 ++ [F7] = L6491 from rfl, show [F1] ++ L6492 = L6489 from rfl,
    show L6492 ++ [F7] = L6490 from rfl] at h
  rw [i3781 hinj, i3779 hinj, i3780 hinj, i3782 hinj] at h
  linarith

theorem row1303 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L5600 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5598 := by
  have h := HLm_submod hΓ [F0] L5599 [F210]
  rw [show [F0] ++ L5599 ++ [F210] = L6495 from rfl, show [F0] ++ L5599 = L6493 from rfl,
    show L5599 ++ [F210] = L6494 from rfl] at h
  rw [i3785 hinj, i3783 hinj, i3784 hinj, i3172 hinj] at h
  linarith

theorem row1304 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6352 + (1 : ℝ) * HLm Γ 5 L5628 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6499 := by
  have h := HLm_submod hΓ [F0] L6500 [F2]
  rw [show [F0] ++ L6500 ++ [F2] = L6498 from rfl, show [F0] ++ L6500 = L6496 from rfl,
    show L6500 ++ [F2] = L6497 from rfl] at h
  rw [i3788 hinj, i3786 hinj, i3787 hinj, i3789 hinj] at h
  linarith

theorem row1305 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5434 + (1 : ℝ) * HLm Γ 5 L5616 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5614 := by
  have h := HLm_submod hΓ [F0] L6504 [F2]
  rw [show [F0] ++ L6504 ++ [F2] = L6503 from rfl, show [F0] ++ L6504 = L6501 from rfl,
    show L6504 ++ [F2] = L6502 from rfl] at h
  rw [i3792 hinj, i3790 hinj, i3791 hinj, i3793 hinj] at h
  linarith

theorem row1306 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6352 + (1 : ℝ) * HLm Γ 5 L5357 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6508 := by
  have h := HLm_submod hΓ [F0] L6509 [F2]
  rw [show [F0] ++ L6509 ++ [F2] = L6507 from rfl, show [F0] ++ L6509 = L6505 from rfl,
    show L6509 ++ [F2] = L6506 from rfl] at h
  rw [i3796 hinj, i3794 hinj, i3795 hinj, i3797 hinj] at h
  linarith

theorem row1307 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L6320 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L1731 := by
  have h := HLm_submod hΓ [F0] L6513 [F210]
  rw [show [F0] ++ L6513 ++ [F210] = L6512 from rfl, show [F0] ++ L6513 = L6510 from rfl,
    show L6513 ++ [F210] = L6511 from rfl] at h
  rw [i3800 hinj, i3798 hinj, i3799 hinj, i3801 hinj] at h
  linarith

theorem row1308 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4558 + (1 : ℝ) * HLm Γ 5 L6310 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5632 := by
  have h := HLm_submod hΓ [F0] L5633 [F67]
  rw [show [F0] ++ L5633 ++ [F67] = L6515 from rfl, show [F0] ++ L5633 = L5634 from rfl,
    show L5633 ++ [F67] = L6514 from rfl] at h
  rw [i3803 hinj, i3197 hinj, i3802 hinj, i3196 hinj] at h
  linarith

theorem row1309 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L5658 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5655 := by
  have h := HLm_submod hΓ [F0] L6519 [F210]
  rw [show [F0] ++ L6519 ++ [F210] = L6518 from rfl, show [F0] ++ L6519 = L6516 from rfl,
    show L6519 ++ [F210] = L6517 from rfl] at h
  rw [i3806 hinj, i3804 hinj, i3805 hinj, i3807 hinj] at h
  linarith

theorem row1310 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6520 + (1 : ℝ) * HLm Γ 5 L6522 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6525 := by
  have h := HLm_submod hΓ [F1] L6526 [F0]
  rw [show [F1] ++ L6526 ++ [F0] = L6524 from rfl, show [F1] ++ L6526 = L6521 from rfl,
    show L6526 ++ [F0] = L6523 from rfl] at h
  rw [i3810 hinj, i3808 hinj, i3809 hinj, i3811 hinj] at h
  linarith

theorem row1311 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L5651 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5649 := by
  have h := HLm_submod hΓ [F0] L5650 [F210]
  rw [show [F0] ++ L5650 ++ [F210] = L6529 from rfl, show [F0] ++ L5650 = L6527 from rfl,
    show L5650 ++ [F210] = L6528 from rfl] at h
  rw [i3814 hinj, i3812 hinj, i3813 hinj, i3207 hinj] at h
  linarith

theorem row1312 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5931 + (1 : ℝ) * HLm Γ 5 L5894 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5929 := by
  have h := HLm_submod hΓ [F1] L6533 [F0]
  rw [show [F1] ++ L6533 ++ [F0] = L6532 from rfl, show [F1] ++ L6533 = L6530 from rfl,
    show L6533 ++ [F0] = L6531 from rfl] at h
  rw [i3817 hinj, i3815 hinj, i3816 hinj, i3818 hinj] at h
  linarith

theorem row1313 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L5663 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5661 := by
  have h := HLm_submod hΓ [F0] L6537 [F210]
  rw [show [F0] ++ L6537 ++ [F210] = L6536 from rfl, show [F0] ++ L6537 = L6534 from rfl,
    show L6537 ++ [F210] = L6535 from rfl] at h
  rw [i3821 hinj, i3819 hinj, i3820 hinj, i3822 hinj] at h
  linarith

theorem row1314 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L6539 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6542 := by
  have h := HLm_submod hΓ [F0] L6543 [F210]
  rw [show [F0] ++ L6543 ++ [F210] = L6541 from rfl, show [F0] ++ L6543 = L6538 from rfl,
    show L6543 ++ [F210] = L6540 from rfl] at h
  rw [i3825 hinj, i3823 hinj, i3824 hinj, i3826 hinj] at h
  linarith

theorem row1315 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L6545 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6548 := by
  have h := HLm_submod hΓ [F0] L6549 [F210]
  rw [show [F0] ++ L6549 ++ [F210] = L6547 from rfl, show [F0] ++ L6549 = L6544 from rfl,
    show L6549 ++ [F210] = L6546 from rfl] at h
  rw [i3829 hinj, i3827 hinj, i3828 hinj, i3830 hinj] at h
  linarith

theorem row1316 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L6551 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6554 := by
  have h := HLm_submod hΓ [F0] L6555 [F210]
  rw [show [F0] ++ L6555 ++ [F210] = L6553 from rfl, show [F0] ++ L6555 = L6550 from rfl,
    show L6555 ++ [F210] = L6552 from rfl] at h
  rw [i3833 hinj, i3831 hinj, i3832 hinj, i3834 hinj] at h
  linarith

theorem row1317 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L5681 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5679 := by
  have h := HLm_submod hΓ [F0] L6559 [F210]
  rw [show [F0] ++ L6559 ++ [F210] = L6558 from rfl, show [F0] ++ L6559 = L6556 from rfl,
    show L6559 ++ [F210] = L6557 from rfl] at h
  rw [i3837 hinj, i3835 hinj, i3836 hinj, i3838 hinj] at h
  linarith

theorem row1318 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L5689 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5687 := by
  have h := HLm_submod hΓ [F0] L5688 [F210]
  rw [show [F0] ++ L5688 ++ [F210] = L6562 from rfl, show [F0] ++ L5688 = L6560 from rfl,
    show L5688 ++ [F210] = L6561 from rfl] at h
  rw [i3841 hinj, i3839 hinj, i3840 hinj, i3230 hinj] at h
  linarith

theorem row1319 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L5697 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5695 := by
  have h := HLm_submod hΓ [F0] L6566 [F210]
  rw [show [F0] ++ L6566 ++ [F210] = L6565 from rfl, show [F0] ++ L6566 = L6563 from rfl,
    show L6566 ++ [F210] = L6564 from rfl] at h
  rw [i3844 hinj, i3842 hinj, i3843 hinj, i3845 hinj] at h
  linarith

theorem row1320 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L5713 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5711 := by
  have h := HLm_submod hΓ [F0] L6570 [F210]
  rw [show [F0] ++ L6570 ++ [F210] = L6569 from rfl, show [F0] ++ L6570 = L6567 from rfl,
    show L6570 ++ [F210] = L6568 from rfl] at h
  rw [i3848 hinj, i3846 hinj, i3847 hinj, i3849 hinj] at h
  linarith

theorem row1321 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L5724 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5722 := by
  have h := HLm_submod hΓ [F0] L5723 [F210]
  rw [show [F0] ++ L5723 ++ [F210] = L6573 from rfl, show [F0] ++ L5723 = L6571 from rfl,
    show L5723 ++ [F210] = L6572 from rfl] at h
  rw [i3852 hinj, i3850 hinj, i3851 hinj, i3252 hinj] at h
  linarith

theorem row1322 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L5773 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5769 := by
  have h := HLm_submod hΓ [F0] L6577 [F210]
  rw [show [F0] ++ L6577 ++ [F210] = L6576 from rfl, show [F0] ++ L6577 = L6574 from rfl,
    show L6577 ++ [F210] = L6575 from rfl] at h
  rw [i3855 hinj, i3853 hinj, i3854 hinj, i3856 hinj] at h
  linarith

theorem row1323 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5931 + (1 : ℝ) * HLm Γ 5 L5468 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6274 := by
  have h := HLm_submod hΓ [F1] L6581 [F0]
  rw [show [F1] ++ L6581 ++ [F0] = L6580 from rfl, show [F1] ++ L6581 = L6578 from rfl,
    show L6581 ++ [F0] = L6579 from rfl] at h
  rw [i3859 hinj, i3857 hinj, i3858 hinj, i3860 hinj] at h
  linarith

theorem row1324 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5759 + (1 : ℝ) * HLm Γ 5 L6582 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5757 := by
  have h := HLm_submod hΓ [F1] L5758 [F2]
  rw [show [F1] ++ L5758 ++ [F2] = L6584 from rfl, show [F1] ++ L5758 = L5760 from rfl,
    show L5758 ++ [F2] = L6583 from rfl] at h
  rw [i3862 hinj, i3274 hinj, i3861 hinj, i3273 hinj] at h
  linarith

theorem row1325 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5931 + (1 : ℝ) * HLm Γ 5 L6120 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6588 := by
  have h := HLm_submod hΓ [F1] L6589 [F0]
  rw [show [F1] ++ L6589 ++ [F0] = L6587 from rfl, show [F1] ++ L6589 = L6585 from rfl,
    show L6589 ++ [F0] = L6586 from rfl] at h
  rw [i3865 hinj, i3863 hinj, i3864 hinj, i3866 hinj] at h
  linarith

theorem row1326 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5931 + (1 : ℝ) * HLm Γ 5 L6591 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6594 := by
  have h := HLm_submod hΓ [F1] L6595 [F0]
  rw [show [F1] ++ L6595 ++ [F0] = L6593 from rfl, show [F1] ++ L6595 = L6590 from rfl,
    show L6595 ++ [F0] = L6592 from rfl] at h
  rw [i3869 hinj, i3867 hinj, i3868 hinj, i3870 hinj] at h
  linarith

theorem row1327 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5931 + (1 : ℝ) * HLm Γ 5 L5220 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6599 := by
  have h := HLm_submod hΓ [F1] L6600 [F0]
  rw [show [F1] ++ L6600 ++ [F0] = L6598 from rfl, show [F1] ++ L6600 = L6596 from rfl,
    show L6600 ++ [F0] = L6597 from rfl] at h
  rw [i3873 hinj, i3871 hinj, i3872 hinj, i3874 hinj] at h
  linarith

theorem row1328 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5931 + (1 : ℝ) * HLm Γ 5 L5795 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5793 := by
  have h := HLm_submod hΓ [F1] L6604 [F0]
  rw [show [F1] ++ L6604 ++ [F0] = L6603 from rfl, show [F1] ++ L6604 = L6601 from rfl,
    show L6604 ++ [F0] = L6602 from rfl] at h
  rw [i3877 hinj, i3875 hinj, i3876 hinj, i3878 hinj] at h
  linarith

theorem row1329 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L5809 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5807 := by
  have h := HLm_submod hΓ [F0] L6608 [F210]
  rw [show [F0] ++ L6608 ++ [F210] = L6607 from rfl, show [F0] ++ L6608 = L6605 from rfl,
    show L6608 ++ [F210] = L6606 from rfl] at h
  rw [i3881 hinj, i3879 hinj, i3880 hinj, i3882 hinj] at h
  linarith

theorem row1330 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L5802 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5800 := by
  have h := HLm_submod hΓ [F0] L6612 [F210]
  rw [show [F0] ++ L6612 ++ [F210] = L6611 from rfl, show [F0] ++ L6612 = L6609 from rfl,
    show L6612 ++ [F210] = L6610 from rfl] at h
  rw [i3885 hinj, i3883 hinj, i3884 hinj, i3886 hinj] at h
  linarith

theorem row1331 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5931 + (1 : ℝ) * HLm Γ 5 L5848 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5846 := by
  have h := HLm_submod hΓ [F1] L6616 [F0]
  rw [show [F1] ++ L6616 ++ [F0] = L6615 from rfl, show [F1] ++ L6616 = L6613 from rfl,
    show L6616 ++ [F0] = L6614 from rfl] at h
  rw [i3889 hinj, i3887 hinj, i3888 hinj, i3890 hinj] at h
  linarith

theorem row1332 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5381 + (1 : ℝ) * HLm Γ 5 L6617 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5863 := by
  have h := HLm_submod hΓ [F0] L5864 [F16]
  rw [show [F0] ++ L5864 ++ [F16] = L6619 from rfl, show [F0] ++ L5864 = L5865 from rfl,
    show L5864 ++ [F16] = L6618 from rfl] at h
  rw [i3892 hinj, i3346 hinj, i3891 hinj, i3345 hinj] at h
  linarith

theorem row1333 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5381 + (1 : ℝ) * HLm Γ 5 L6620 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5869 := by
  have h := HLm_submod hΓ [F0] L5870 [F16]
  rw [show [F0] ++ L5870 ++ [F16] = L6622 from rfl, show [F0] ++ L5870 = L5871 from rfl,
    show L5870 ++ [F16] = L6621 from rfl] at h
  rw [i3894 hinj, i3350 hinj, i3893 hinj, i3349 hinj] at h
  linarith

theorem row1334 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L5878 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5876 := by
  have h := HLm_submod hΓ [F0] L5877 [F210]
  rw [show [F0] ++ L5877 ++ [F210] = L6625 from rfl, show [F0] ++ L5877 = L6623 from rfl,
    show L5877 ++ [F210] = L6624 from rfl] at h
  rw [i3897 hinj, i3895 hinj, i3896 hinj, i3353 hinj] at h
  linarith

theorem row1335 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5489 + (1 : ℝ) * HLm Γ 5 L5912 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5910 := by
  have h := HLm_submod hΓ [F0] L6629 [F1]
  rw [show [F0] ++ L6629 ++ [F1] = L6628 from rfl, show [F0] ++ L6629 = L6626 from rfl,
    show L6629 ++ [F1] = L6627 from rfl] at h
  rw [i3900 hinj, i3898 hinj, i3899 hinj, i3901 hinj] at h
  linarith

theorem row1336 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L5919 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5917 := by
  have h := HLm_submod hΓ [F0] L6633 [F210]
  rw [show [F0] ++ L6633 ++ [F210] = L6632 from rfl, show [F0] ++ L6633 = L6630 from rfl,
    show L6633 ++ [F210] = L6631 from rfl] at h
  rw [i3904 hinj, i3902 hinj, i3903 hinj, i3905 hinj] at h
  linarith

theorem row1337 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L6062 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6059 := by
  have h := HLm_submod hΓ [F0] L6637 [F210]
  rw [show [F0] ++ L6637 ++ [F210] = L6636 from rfl, show [F0] ++ L6637 = L6634 from rfl,
    show L6637 ++ [F210] = L6635 from rfl] at h
  rw [i3908 hinj, i3906 hinj, i3907 hinj, i3909 hinj] at h
  linarith

theorem row1338 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L6195 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6191 := by
  have h := HLm_submod hΓ [F0] L6641 [F210]
  rw [show [F0] ++ L6641 ++ [F210] = L6640 from rfl, show [F0] ++ L6641 = L6638 from rfl,
    show L6641 ++ [F210] = L6639 from rfl] at h
  rw [i3912 hinj, i3910 hinj, i3911 hinj, i3913 hinj] at h
  linarith

theorem row1339 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L5938 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5936 := by
  have h := HLm_submod hΓ [F0] L5937 [F210]
  rw [show [F0] ++ L5937 ++ [F210] = L6644 from rfl, show [F0] ++ L5937 = L6642 from rfl,
    show L5937 ++ [F210] = L6643 from rfl] at h
  rw [i3916 hinj, i3914 hinj, i3915 hinj, i3390 hinj] at h
  linarith

theorem row1340 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L5946 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5942 := by
  have h := HLm_submod hΓ [F0] L6648 [F210]
  rw [show [F0] ++ L6648 ++ [F210] = L6647 from rfl, show [F0] ++ L6648 = L6645 from rfl,
    show L6648 ++ [F210] = L6646 from rfl] at h
  rw [i3919 hinj, i3917 hinj, i3918 hinj, i3920 hinj] at h
  linarith

theorem row1341 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L6306 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6303 := by
  have h := HLm_submod hΓ [F0] L6304 [F210]
  rw [show [F0] ++ L6304 ++ [F210] = L6650 from rfl, show [F0] ++ L6304 = L6649 from rfl,
    show L6304 ++ [F210] = L6307 from rfl] at h
  rw [i3922 hinj, i3921 hinj, i3637 hinj, i3635 hinj] at h
  linarith

theorem row1342 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5668 + (1 : ℝ) * HLm Γ 5 L6652 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6655 := by
  have h := HLm_submod hΓ [F0] L6656 [F2]
  rw [show [F0] ++ L6656 ++ [F2] = L6654 from rfl, show [F0] ++ L6656 = L6651 from rfl,
    show L6656 ++ [F2] = L6653 from rfl] at h
  rw [i3925 hinj, i3923 hinj, i3924 hinj, i3926 hinj] at h
  linarith

theorem row1343 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L6658 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6661 := by
  have h := HLm_submod hΓ [F0] L6662 [F210]
  rw [show [F0] ++ L6662 ++ [F210] = L6660 from rfl, show [F0] ++ L6662 = L6657 from rfl,
    show L6662 ++ [F210] = L6659 from rfl] at h
  rw [i3929 hinj, i3927 hinj, i3928 hinj, i3930 hinj] at h
  linarith

theorem row1344 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L6219 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6216 := by
  have h := HLm_submod hΓ [F0] L6666 [F210]
  rw [show [F0] ++ L6666 ++ [F210] = L6665 from rfl, show [F0] ++ L6666 = L6663 from rfl,
    show L6666 ++ [F210] = L6664 from rfl] at h
  rw [i3933 hinj, i3931 hinj, i3932 hinj, i3934 hinj] at h
  linarith

theorem row1345 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L5967 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5965 := by
  have h := HLm_submod hΓ [F0] L5966 [F210]
  rw [show [F0] ++ L5966 ++ [F210] = L6669 from rfl, show [F0] ++ L5966 = L6667 from rfl,
    show L5966 ++ [F210] = L6668 from rfl] at h
  rw [i3937 hinj, i3935 hinj, i3936 hinj, i3406 hinj] at h
  linarith

theorem row1346 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L5975 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5973 := by
  have h := HLm_submod hΓ [F0] L5974 [F210]
  rw [show [F0] ++ L5974 ++ [F210] = L6672 from rfl, show [F0] ++ L5974 = L6670 from rfl,
    show L5974 ++ [F210] = L6671 from rfl] at h
  rw [i3940 hinj, i3938 hinj, i3939 hinj, i3410 hinj] at h
  linarith

theorem row1347 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L6005 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6002 := by
  have h := HLm_submod hΓ [F0] L6676 [F210]
  rw [show [F0] ++ L6676 ++ [F210] = L6675 from rfl, show [F0] ++ L6676 = L6673 from rfl,
    show L6676 ++ [F210] = L6674 from rfl] at h
  rw [i3943 hinj, i3941 hinj, i3942 hinj, i3944 hinj] at h
  linarith

theorem row1348 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L6678 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6681 := by
  have h := HLm_submod hΓ [F0] L6682 [F210]
  rw [show [F0] ++ L6682 ++ [F210] = L6680 from rfl, show [F0] ++ L6682 = L6677 from rfl,
    show L6682 ++ [F210] = L6679 from rfl] at h
  rw [i3947 hinj, i3945 hinj, i3946 hinj, i3948 hinj] at h
  linarith

theorem row1349 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L5994 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5992 := by
  have h := HLm_submod hΓ [F0] L6686 [F210]
  rw [show [F0] ++ L6686 ++ [F210] = L6685 from rfl, show [F0] ++ L6686 = L6683 from rfl,
    show L6686 ++ [F210] = L6684 from rfl] at h
  rw [i3951 hinj, i3949 hinj, i3950 hinj, i3952 hinj] at h
  linarith

end EntropyBounds.TwoSet.Certs.R7A5
