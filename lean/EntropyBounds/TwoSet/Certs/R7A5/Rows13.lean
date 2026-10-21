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

theorem row1950 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9471 + (1 : ℝ) * HLm Γ 5 L9473 + (-1 : ℝ) * HLm Γ 5 L9475 + (-1 : ℝ) * HLm Γ 5 L7900 := by
  have h := HLm_submod hΓ [F210] L9477 [F6]
  rw [show [F210] ++ L9477 ++ [F6] = L9476 from rfl, show [F210] ++ L9477 = L9472 from rfl,
    show L9477 ++ [F6] = L9474 from rfl] at h
  rw [i5597 hinj, i5595 hinj, i5596 hinj, i5598 hinj] at h
  linarith

theorem row1951 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9478 + (1 : ℝ) * HLm Γ 5 L9480 + (-1 : ℝ) * HLm Γ 5 L9482 + (-1 : ℝ) * HLm Γ 5 L3995 := by
  have h := HLm_submod hΓ [F1] L9484 [F34]
  rw [show [F1] ++ L9484 ++ [F34] = L9483 from rfl, show [F1] ++ L9484 = L9479 from rfl,
    show L9484 ++ [F34] = L9481 from rfl] at h
  rw [i5601 hinj, i5599 hinj, i5600 hinj, i5602 hinj] at h
  linarith

theorem row1952 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2241 + (1 : ℝ) * HLm Γ 5 L4009 + (-1 : ℝ) * HLm Γ 5 L2670 + (-1 : ℝ) * HLm Γ 5 L3048 := by
  have h := HLm_submod hΓ [F0] L3049 [F3]
  rw [show [F0] ++ L3049 ++ [F3] = L9487 from rfl, show [F0] ++ L3049 = L9485 from rfl,
    show L3049 ++ [F3] = L9486 from rfl] at h
  rw [i5605 hinj, i5603 hinj, i5604 hinj, i1734 hinj] at h
  linarith

theorem row1953 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9488 + (1 : ℝ) * HLm Γ 5 L9490 + (-1 : ℝ) * HLm Γ 5 L9492 + (-1 : ℝ) * HLm Γ 5 L7921 := by
  have h := HLm_submod hΓ [F51] L9494 [F210]
  rw [show [F51] ++ L9494 ++ [F210] = L9493 from rfl, show [F51] ++ L9494 = L9489 from rfl,
    show L9494 ++ [F210] = L9491 from rfl] at h
  rw [i5608 hinj, i5606 hinj, i5607 hinj, i5609 hinj] at h
  linarith

theorem row1954 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9495 + (1 : ℝ) * HLm Γ 5 L8059 + (-1 : ℝ) * HLm Γ 5 L9498 + (-1 : ℝ) * HLm Γ 5 L8057 := by
  have h := HLm_submod hΓ [F51] L9500 [F16]
  rw [show [F51] ++ L9500 ++ [F16] = L9499 from rfl, show [F51] ++ L9500 = L9496 from rfl,
    show L9500 ++ [F16] = L9497 from rfl] at h
  rw [i5612 hinj, i5610 hinj, i5611 hinj, i5613 hinj] at h
  linarith

theorem row1955 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7194 + (1 : ℝ) * HLm Γ 5 L7923 + (-1 : ℝ) * HLm Γ 5 L9503 + (-1 : ℝ) * HLm Γ 5 L8089 := by
  have h := HLm_submod hΓ [F0] L9505 [F23]
  rw [show [F0] ++ L9505 ++ [F23] = L9504 from rfl, show [F0] ++ L9505 = L9501 from rfl,
    show L9505 ++ [F23] = L9502 from rfl] at h
  rw [i5616 hinj, i5614 hinj, i5615 hinj, i5617 hinj] at h
  linarith

theorem row1956 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7622 + (1 : ℝ) * HLm Γ 5 L7673 + (-1 : ℝ) * HLm Γ 5 L9508 + (-1 : ℝ) * HLm Γ 5 L7943 := by
  have h := HLm_submod hΓ [F44] L7944 [F16]
  rw [show [F44] ++ L7944 ++ [F16] = L9509 from rfl, show [F44] ++ L7944 = L9506 from rfl,
    show L7944 ++ [F16] = L9507 from rfl] at h
  rw [i5620 hinj, i5618 hinj, i5619 hinj, i4685 hinj] at h
  linarith

theorem row1957 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8033 + (1 : ℝ) * HLm Γ 5 L9511 + (-1 : ℝ) * HLm Γ 5 L9513 + (-1 : ℝ) * HLm Γ 5 L8031 := by
  have h := HLm_submod hΓ [F2] L9515 [F68]
  rw [show [F2] ++ L9515 ++ [F68] = L9514 from rfl, show [F2] ++ L9515 = L9510 from rfl,
    show L9515 ++ [F68] = L9512 from rfl] at h
  rw [i5623 hinj, i5621 hinj, i5622 hinj, i5624 hinj] at h
  linarith

theorem row1958 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4530 + (1 : ℝ) * HLm Γ 5 L9517 + (-1 : ℝ) * HLm Γ 5 L9519 + (-1 : ℝ) * HLm Γ 5 L7951 := by
  have h := HLm_submod hΓ [F7] L9521 [F12]
  rw [show [F7] ++ L9521 ++ [F12] = L9520 from rfl, show [F7] ++ L9521 = L9516 from rfl,
    show L9521 ++ [F12] = L9518 from rfl] at h
  rw [i5627 hinj, i5625 hinj, i5626 hinj, i5628 hinj] at h
  linarith

theorem row1959 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7961 + (1 : ℝ) * HLm Γ 5 L9522 + (-1 : ℝ) * HLm Γ 5 L5322 + (-1 : ℝ) * HLm Γ 5 L7959 := by
  have h := HLm_submod hΓ [F1] L7960 [F16]
  rw [show [F1] ++ L7960 ++ [F16] = L9524 from rfl, show [F1] ++ L7960 = L7962 from rfl,
    show L7960 ++ [F16] = L9523 from rfl] at h
  rw [i5630 hinj, i4694 hinj, i5629 hinj, i4693 hinj] at h
  linarith

theorem row1960 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9525 + (1 : ℝ) * HLm Γ 5 L9295 + (-1 : ℝ) * HLm Γ 5 L9297 + (-1 : ℝ) * HLm Γ 5 L4072 := by
  have h := HLm_submod hΓ [F7] L4073 [F108]
  rw [show [F7] ++ L4073 ++ [F108] = L9528 from rfl, show [F7] ++ L4073 = L9526 from rfl,
    show L4073 ++ [F108] = L9527 from rfl] at h
  rw [i5633 hinj, i5631 hinj, i5632 hinj, i2272 hinj] at h
  linarith

theorem row1961 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1182 + (1 : ℝ) * HLm Γ 5 L7972 + (-1 : ℝ) * HLm Γ 5 L9531 + (-1 : ℝ) * HLm Γ 5 L7970 := by
  have h := HLm_submod hΓ [F0] L9533 [F210]
  rw [show [F0] ++ L9533 ++ [F210] = L9532 from rfl, show [F0] ++ L9533 = L9529 from rfl,
    show L9533 ++ [F210] = L9530 from rfl] at h
  rw [i5636 hinj, i5634 hinj, i5635 hinj, i5637 hinj] at h
  linarith

theorem row1962 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9534 + (1 : ℝ) * HLm Γ 5 L7978 + (-1 : ℝ) * HLm Γ 5 L9537 + (-1 : ℝ) * HLm Γ 5 L7976 := by
  have h := HLm_submod hΓ [F52] L7977 [F228]
  rw [show [F52] ++ L7977 ++ [F228] = L9538 from rfl, show [F52] ++ L7977 = L9535 from rfl,
    show L7977 ++ [F228] = L9536 from rfl] at h
  rw [i5640 hinj, i5638 hinj, i5639 hinj, i4702 hinj] at h
  linarith

theorem row1963 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7984 + (1 : ℝ) * HLm Γ 5 L9539 + (-1 : ℝ) * HLm Γ 5 L9460 + (-1 : ℝ) * HLm Γ 5 L7982 := by
  have h := HLm_submod hΓ [F7] L7983 [F67]
  rw [show [F7] ++ L7983 ++ [F67] = L9541 from rfl, show [F7] ++ L7983 = L7985 from rfl,
    show L7983 ++ [F67] = L9540 from rfl] at h
  rw [i5642 hinj, i4706 hinj, i5641 hinj, i4705 hinj] at h
  linarith

theorem row1964 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9542 + (1 : ℝ) * HLm Γ 5 L9544 + (-1 : ℝ) * HLm Γ 5 L9546 + (-1 : ℝ) * HLm Γ 5 L8036 := by
  have h := HLm_submod hΓ [F44] L9548 [F210]
  rw [show [F44] ++ L9548 ++ [F210] = L9547 from rfl, show [F44] ++ L9548 = L9543 from rfl,
    show L9548 ++ [F210] = L9545 from rfl] at h
  rw [i5645 hinj, i5643 hinj, i5644 hinj, i5646 hinj] at h
  linarith

theorem row1965 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9549 + (1 : ℝ) * HLm Γ 5 L8072 + (-1 : ℝ) * HLm Γ 5 L9552 + (-1 : ℝ) * HLm Γ 5 L8070 := by
  have h := HLm_submod hΓ [F107] L9554 [F210]
  rw [show [F107] ++ L9554 ++ [F210] = L9553 from rfl, show [F107] ++ L9554 = L9550 from rfl,
    show L9554 ++ [F210] = L9551 from rfl] at h
  rw [i5649 hinj, i5647 hinj, i5648 hinj, i5650 hinj] at h
  linarith

theorem row1966 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9555 + (1 : ℝ) * HLm Γ 5 L8100 + (-1 : ℝ) * HLm Γ 5 L9558 + (-1 : ℝ) * HLm Γ 5 L8098 := by
  have h := HLm_submod hΓ [F1] L8099 [F46]
  rw [show [F1] ++ L8099 ++ [F46] = L9559 from rfl, show [F1] ++ L8099 = L9556 from rfl,
    show L8099 ++ [F46] = L9557 from rfl] at h
  rw [i5653 hinj, i5651 hinj, i5652 hinj, i4776 hinj] at h
  linarith

theorem row1967 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L9561 + (-1 : ℝ) * HLm Γ 5 L4558 + (-1 : ℝ) * HLm Γ 5 L558 := by
  have h := HLm_submod hΓ [F7] L9564 [F217]
  rw [show [F7] ++ L9564 ++ [F217] = L9563 from rfl, show [F7] ++ L9564 = L9560 from rfl,
    show L9564 ++ [F217] = L9562 from rfl] at h
  rw [i5656 hinj, i5654 hinj, i5655 hinj, i5657 hinj] at h
  linarith

theorem row1968 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9565 + (1 : ℝ) * HLm Γ 5 L8123 + (-1 : ℝ) * HLm Γ 5 L9568 + (-1 : ℝ) * HLm Γ 5 L8121 := by
  have h := HLm_submod hΓ [F22] L8122 [F210]
  rw [show [F22] ++ L8122 ++ [F210] = L9569 from rfl, show [F22] ++ L8122 = L9566 from rfl,
    show L8122 ++ [F210] = L9567 from rfl] at h
  rw [i5660 hinj, i5658 hinj, i5659 hinj, i4788 hinj] at h
  linarith

theorem row1969 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L1350 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L8125 := by
  have h := HLm_submod hΓ [F7] L8126 [F67]
  rw [show [F7] ++ L8126 ++ [F67] = L9571 from rfl, show [F7] ++ L8126 = L8127 from rfl,
    show L8126 ++ [F67] = L9570 from rfl] at h
  rw [i5662 hinj, i4791 hinj, i5661 hinj, i4790 hinj] at h
  linarith

theorem row1970 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L842 + (1 : ℝ) * HLm Γ 5 L4329 + (-1 : ℝ) * HLm Γ 5 L5381 + (-1 : ℝ) * HLm Γ 5 L731 := by
  have h := HLm_submod hΓ [F7] L4326 [F210]
  rw [show [F7] ++ L4326 ++ [F210] = L9573 from rfl, show [F7] ++ L4326 = L9572 from rfl,
    show L4326 ++ [F210] = L4330 from rfl] at h
  rw [i5664 hinj, i5663 hinj, i2428 hinj, i2426 hinj] at h
  linarith

theorem row1971 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L8132 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L8128 := by
  have h := HLm_submod hΓ [F1] L9577 [F67]
  rw [show [F1] ++ L9577 ++ [F67] = L9576 from rfl, show [F1] ++ L9577 = L9574 from rfl,
    show L9577 ++ [F67] = L9575 from rfl] at h
  rw [i5667 hinj, i5665 hinj, i5666 hinj, i5668 hinj] at h
  linarith

theorem row1972 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9578 + (1 : ℝ) * HLm Γ 5 L8523 + (-1 : ℝ) * HLm Γ 5 L4558 + (-1 : ℝ) * HLm Γ 5 L9582 := by
  have h := HLm_submod hΓ [F1] L9583 [F7]
  rw [show [F1] ++ L9583 ++ [F7] = L9581 from rfl, show [F1] ++ L9583 = L9579 from rfl,
    show L9583 ++ [F7] = L9580 from rfl] at h
  rw [i5671 hinj, i5669 hinj, i5670 hinj, i5672 hinj] at h
  linarith

theorem row1973 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9584 + (1 : ℝ) * HLm Γ 5 L9586 + (-1 : ℝ) * HLm Γ 5 L9588 + (-1 : ℝ) * HLm Γ 5 L8141 := by
  have h := HLm_submod hΓ [F67] L9590 [F36]
  rw [show [F67] ++ L9590 ++ [F36] = L9589 from rfl, show [F67] ++ L9590 = L9585 from rfl,
    show L9590 ++ [F36] = L9587 from rfl] at h
  rw [i5675 hinj, i5673 hinj, i5674 hinj, i5676 hinj] at h
  linarith

theorem row1974 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L847 + (1 : ℝ) * HLm Γ 5 L9592 + (-1 : ℝ) * HLm Γ 5 L5489 + (-1 : ℝ) * HLm Γ 5 L8240 := by
  have h := HLm_submod hΓ [F7] L9595 [F210]
  rw [show [F7] ++ L9595 ++ [F210] = L9594 from rfl, show [F7] ++ L9595 = L9591 from rfl,
    show L9595 ++ [F210] = L9593 from rfl] at h
  rw [i5679 hinj, i5677 hinj, i5678 hinj, i5680 hinj] at h
  linarith

theorem row1975 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L9597 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L9600 := by
  have h := HLm_submod hΓ [F4] L9601 [F210]
  rw [show [F4] ++ L9601 ++ [F210] = L9599 from rfl, show [F4] ++ L9601 = L9596 from rfl,
    show L9601 ++ [F210] = L9598 from rfl] at h
  rw [i5683 hinj, i5681 hinj, i5682 hinj, i5684 hinj] at h
  linarith

theorem row1976 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5438 + (1 : ℝ) * HLm Γ 5 L9602 + (-1 : ℝ) * HLm Γ 5 L9604 + (-1 : ℝ) * HLm Γ 5 L597 := by
  have h := HLm_submod hΓ [F210] L597 [F36]
  rw [show [F210] ++ L597 ++ [F36] = L9605 from rfl, show [F210] ++ L597 = L5439 from rfl,
    show L597 ++ [F36] = L9603 from rfl] at h
  rw [i5686 hinj, i3071 hinj, i5685 hinj] at h
  linarith

theorem row1977 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L8306 + (-1 : ℝ) * HLm Γ 5 L4558 + (-1 : ℝ) * HLm Γ 5 L8154 := by
  have h := HLm_submod hΓ [F1] L9609 [F217]
  rw [show [F1] ++ L9609 ++ [F217] = L9608 from rfl, show [F1] ++ L9609 = L9606 from rfl,
    show L9609 ++ [F217] = L9607 from rfl] at h
  rw [i5689 hinj, i5687 hinj, i5688 hinj, i5690 hinj] at h
  linarith

theorem row1978 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9610 + (1 : ℝ) * HLm Γ 5 L5451 + (-1 : ℝ) * HLm Γ 5 L9613 + (-1 : ℝ) * HLm Γ 5 L1332 := by
  have h := HLm_submod hΓ [F107] L5457 [F210]
  rw [show [F107] ++ L5457 ++ [F210] = L9614 from rfl, show [F107] ++ L5457 = L9611 from rfl,
    show L5457 ++ [F210] = L9612 from rfl] at h
  rw [i5693 hinj, i5691 hinj, i5692 hinj, i3081 hinj] at h
  linarith

theorem row1979 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9615 + (1 : ℝ) * HLm Γ 5 L9617 + (-1 : ℝ) * HLm Γ 5 L9619 + (-1 : ℝ) * HLm Γ 5 L9621 := by
  have h := HLm_submod hΓ [F210] L9622 [F43]
  rw [show [F210] ++ L9622 ++ [F43] = L9620 from rfl, show [F210] ++ L9622 = L9616 from rfl,
    show L9622 ++ [F43] = L9618 from rfl] at h
  rw [i5696 hinj, i5694 hinj, i5695 hinj, i5697 hinj] at h
  linarith

theorem row1980 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5244 + (1 : ℝ) * HLm Γ 5 L9624 + (-1 : ℝ) * HLm Γ 5 L9626 + (-1 : ℝ) * HLm Γ 5 L9628 := by
  have h := HLm_submod hΓ [F210] L9629 [F25]
  rw [show [F210] ++ L9629 ++ [F25] = L9627 from rfl, show [F210] ++ L9629 = L9623 from rfl,
    show L9629 ++ [F25] = L9625 from rfl] at h
  rw [i5700 hinj, i5698 hinj, i5699 hinj, i5701 hinj] at h
  linarith

theorem row1981 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5472 + (1 : ℝ) * HLm Γ 5 L9630 + (-1 : ℝ) * HLm Γ 5 L9632 + (-1 : ℝ) * HLm Γ 5 L5478 := by
  have h := HLm_submod hΓ [F210] L5479 [F36]
  rw [show [F210] ++ L5479 ++ [F36] = L9633 from rfl, show [F210] ++ L5479 = L5473 from rfl,
    show L5479 ++ [F36] = L9631 from rfl] at h
  rw [i5703 hinj, i3090 hinj, i5702 hinj, i3093 hinj] at h
  linarith

theorem row1982 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5474 + (1 : ℝ) * HLm Γ 5 L8165 + (-1 : ℝ) * HLm Γ 5 L5476 + (-1 : ℝ) * HLm Γ 5 L8163 := by
  have h := HLm_submod hΓ [F23] L8164 [F210]
  rw [show [F23] ++ L8164 ++ [F210] = L9636 from rfl, show [F23] ++ L8164 = L9634 from rfl,
    show L8164 ++ [F210] = L9635 from rfl] at h
  rw [i5706 hinj, i5704 hinj, i5705 hinj, i4815 hinj] at h
  linarith

theorem row1983 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4366 + (1 : ℝ) * HLm Γ 5 L8172 + (-1 : ℝ) * HLm Γ 5 L5381 + (-1 : ℝ) * HLm Γ 5 L8170 := by
  have h := HLm_submod hΓ [F1] L9131 [F7]
  rw [show [F1] ++ L9131 ++ [F7] = L9639 from rfl, show [F1] ++ L9131 = L9637 from rfl,
    show L9131 ++ [F7] = L9638 from rfl] at h
  rw [i5709 hinj, i5707 hinj, i5708 hinj, i5398 hinj] at h
  linarith

theorem row1984 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L9165 + (-1 : ℝ) * HLm Γ 5 L4558 + (-1 : ℝ) * HLm Γ 5 L1281 := by
  have h := HLm_submod hΓ [F1] L1814 [F217]
  rw [show [F1] ++ L1814 ++ [F217] = L9641 from rfl, show [F1] ++ L1814 = L1811 from rfl,
    show L1814 ++ [F217] = L9640 from rfl] at h
  rw [i5711 hinj, i962 hinj, i5710 hinj, i965 hinj] at h
  linarith

theorem row1985 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8143 + (1 : ℝ) * HLm Γ 5 L9643 + (-1 : ℝ) * HLm Γ 5 L6087 + (-1 : ℝ) * HLm Γ 5 L8175 := by
  have h := HLm_submod hΓ [F7] L8176 [F67]
  rw [show [F7] ++ L8176 ++ [F67] = L9645 from rfl, show [F7] ++ L8176 = L9642 from rfl,
    show L8176 ++ [F67] = L9644 from rfl] at h
  rw [i5714 hinj, i5712 hinj, i5713 hinj, i4822 hinj] at h
  linarith

theorem row1986 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L9646 + (-1 : ℝ) * HLm Γ 5 L4558 + (-1 : ℝ) * HLm Γ 5 L1819 := by
  have h := HLm_submod hΓ [F1] L1820 [F218]
  rw [show [F1] ++ L1820 ++ [F218] = L9648 from rfl, show [F1] ++ L1820 = L1815 from rfl,
    show L1820 ++ [F218] = L9647 from rfl] at h
  rw [i5716 hinj, i966 hinj, i5715 hinj, i969 hinj] at h
  linarith

theorem row1987 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1285 + (1 : ℝ) * HLm Γ 5 L8311 + (-1 : ℝ) * HLm Γ 5 L9651 + (-1 : ℝ) * HLm Γ 5 L8308 := by
  have h := HLm_submod hΓ [F16] L9653 [F210]
  rw [show [F16] ++ L9653 ++ [F210] = L9652 from rfl, show [F16] ++ L9653 = L9649 from rfl,
    show L9653 ++ [F210] = L9650 from rfl] at h
  rw [i5719 hinj, i5717 hinj, i5718 hinj, i5720 hinj] at h
  linarith

theorem row1988 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8183 + (1 : ℝ) * HLm Γ 5 L9655 + (-1 : ℝ) * HLm Γ 5 L9657 + (-1 : ℝ) * HLm Γ 5 L8181 := by
  have h := HLm_submod hΓ [F210] L9659 [F25]
  rw [show [F210] ++ L9659 ++ [F25] = L9658 from rfl, show [F210] ++ L9659 = L9654 from rfl,
    show L9659 ++ [F25] = L9656 from rfl] at h
  rw [i5723 hinj, i5721 hinj, i5722 hinj, i5724 hinj] at h
  linarith

theorem row1989 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L8211 + (-1 : ℝ) * HLm Γ 5 L4558 + (-1 : ℝ) * HLm Γ 5 L8207 := by
  have h := HLm_submod hΓ [F1] L9663 [F217]
  rw [show [F1] ++ L9663 ++ [F217] = L9662 from rfl, show [F1] ++ L9663 = L9660 from rfl,
    show L9663 ++ [F217] = L9661 from rfl] at h
  rw [i5727 hinj, i5725 hinj, i5726 hinj, i5728 hinj] at h
  linarith

theorem row1990 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8190 + (1 : ℝ) * HLm Γ 5 L9665 + (-1 : ℝ) * HLm Γ 5 L9667 + (-1 : ℝ) * HLm Γ 5 L9669 := by
  have h := HLm_submod hΓ [F67] L9670 [F36]
  rw [show [F67] ++ L9670 ++ [F36] = L9668 from rfl, show [F67] ++ L9670 = L9664 from rfl,
    show L9670 ++ [F36] = L9666 from rfl] at h
  rw [i5731 hinj, i5729 hinj, i5730 hinj, i5732 hinj] at h
  linarith

theorem row1991 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1301 + (1 : ℝ) * HLm Γ 5 L5487 + (-1 : ℝ) * HLm Γ 5 L9671 + (-1 : ℝ) * HLm Γ 5 L989 := by
  have h := HLm_submod hΓ [F1] L1300 [F210]
  rw [show [F1] ++ L1300 ++ [F210] = L9672 from rfl, show [F1] ++ L1300 = L1302 from rfl,
    show L1300 ++ [F210] = L5488 from rfl] at h
  rw [i5733 hinj, i640 hinj, i3099 hinj, i639 hinj] at h
  linarith

theorem row1992 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8196 + (1 : ℝ) * HLm Γ 5 L9673 + (-1 : ℝ) * HLm Γ 5 L9675 + (-1 : ℝ) * HLm Γ 5 L8194 := by
  have h := HLm_submod hΓ [F210] L8195 [F43]
  rw [show [F210] ++ L8195 ++ [F43] = L9676 from rfl, show [F210] ++ L8195 = L8197 from rfl,
    show L8195 ++ [F43] = L9674 from rfl] at h
  rw [i5735 hinj, i4833 hinj, i5734 hinj, i4832 hinj] at h
  linarith

theorem row1993 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8202 + (1 : ℝ) * HLm Γ 5 L9678 + (-1 : ℝ) * HLm Γ 5 L9680 + (-1 : ℝ) * HLm Γ 5 L8200 := by
  have h := HLm_submod hΓ [F210] L9682 [F33]
  rw [show [F210] ++ L9682 ++ [F33] = L9681 from rfl, show [F210] ++ L9682 = L9677 from rfl,
    show L9682 ++ [F33] = L9679 from rfl] at h
  rw [i5738 hinj, i5736 hinj, i5737 hinj, i5739 hinj] at h
  linarith

theorem row1994 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9683 + (1 : ℝ) * HLm Γ 5 L9370 + (-1 : ℝ) * HLm Γ 5 L9686 + (-1 : ℝ) * HLm Γ 5 L8326 := by
  have h := HLm_submod hΓ [F62] L9688 [F210]
  rw [show [F62] ++ L9688 ++ [F210] = L9687 from rfl, show [F62] ++ L9688 = L9684 from rfl,
    show L9688 ++ [F210] = L9685 from rfl] at h
  rw [i5742 hinj, i5740 hinj, i5741 hinj, i5743 hinj] at h
  linarith

theorem row1995 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9689 + (1 : ℝ) * HLm Γ 5 L9206 + (-1 : ℝ) * HLm Γ 5 L9692 + (-1 : ℝ) * HLm Γ 5 L8304 := by
  have h := HLm_submod hΓ [F107] L9694 [F67]
  rw [show [F107] ++ L9694 ++ [F67] = L9693 from rfl, show [F107] ++ L9694 = L9690 from rfl,
    show L9694 ++ [F67] = L9691 from rfl] at h
  rw [i5746 hinj, i5744 hinj, i5745 hinj, i5747 hinj] at h
  linarith

theorem row1996 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8211 + (1 : ℝ) * HLm Γ 5 L9240 + (-1 : ℝ) * HLm Γ 5 L9696 + (-1 : ℝ) * HLm Γ 5 L8209 := by
  have h := HLm_submod hΓ [F46] L8210 [F67]
  rw [show [F46] ++ L8210 ++ [F67] = L9697 from rfl, show [F46] ++ L8210 = L8212 from rfl,
    show L8210 ++ [F67] = L9695 from rfl] at h
  rw [i5749 hinj, i4842 hinj, i5748 hinj, i4841 hinj] at h
  linarith

theorem row1997 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8515 + (1 : ℝ) * HLm Γ 5 L9699 + (-1 : ℝ) * HLm Γ 5 L9701 + (-1 : ℝ) * HLm Γ 5 L9703 := by
  have h := HLm_submod hΓ [F7] L9704 [F3]
  rw [show [F7] ++ L9704 ++ [F3] = L9702 from rfl, show [F7] ++ L9704 = L9698 from rfl,
    show L9704 ++ [F3] = L9700 from rfl] at h
  rw [i5752 hinj, i5750 hinj, i5751 hinj, i5753 hinj] at h
  linarith

theorem row1998 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8217 + (1 : ℝ) * HLm Γ 5 L5502 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L8215 := by
  have h := HLm_submod hΓ [F7] L8216 [F4]
  rw [show [F7] ++ L8216 ++ [F4] = L9706 from rfl, show [F7] ++ L8216 = L8218 from rfl,
    show L8216 ++ [F4] = L9705 from rfl] at h
  rw [i5755 hinj, i4845 hinj, i5754 hinj, i4844 hinj] at h
  linarith

theorem row1999 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8934 + (1 : ℝ) * HLm Γ 5 L8232 + (-1 : ℝ) * HLm Γ 5 L6462 + (-1 : ℝ) * HLm Γ 5 L8230 := by
  have h := HLm_submod hΓ [F7] L8231 [F210]
  rw [show [F7] ++ L8231 ++ [F210] = L9709 from rfl, show [F7] ++ L8231 = L9707 from rfl,
    show L8231 ++ [F210] = L9708 from rfl] at h
  rw [i5758 hinj, i5756 hinj, i5757 hinj, i4851 hinj] at h
  linarith

theorem row2000 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5739 + (1 : ℝ) * HLm Γ 5 L9711 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L8242 := by
  have h := HLm_submod hΓ [F7] L8243 [F4]
  rw [show [F7] ++ L8243 ++ [F4] = L9713 from rfl, show [F7] ++ L8243 = L9710 from rfl,
    show L8243 ++ [F4] = L9712 from rfl] at h
  rw [i5761 hinj, i5759 hinj, i5760 hinj, i4858 hinj] at h
  linarith

theorem row2001 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8279 + (1 : ℝ) * HLm Γ 5 L8329 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L9717 := by
  have h := HLm_submod hΓ [F7] L9718 [F16]
  rw [show [F7] ++ L9718 ++ [F16] = L9716 from rfl, show [F7] ++ L9718 = L9714 from rfl,
    show L9718 ++ [F16] = L9715 from rfl] at h
  rw [i5764 hinj, i5762 hinj, i5763 hinj, i5765 hinj] at h
  linarith

theorem row2002 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8255 + (1 : ℝ) * HLm Γ 5 L9719 + (-1 : ℝ) * HLm Γ 5 L9721 + (-1 : ℝ) * HLm Γ 5 L8253 := by
  have h := HLm_submod hΓ [F7] L8254 [F2]
  rw [show [F7] ++ L8254 ++ [F2] = L9722 from rfl, show [F7] ++ L8254 = L8256 from rfl,
    show L8254 ++ [F2] = L9720 from rfl] at h
  rw [i5767 hinj, i4865 hinj, i5766 hinj, i4864 hinj] at h
  linarith

theorem row2003 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4842 + (1 : ℝ) * HLm Γ 5 L9723 + (-1 : ℝ) * HLm Γ 5 L9725 + (-1 : ℝ) * HLm Γ 5 L5549 := by
  have h := HLm_submod hΓ [F7] L5550 [F3]
  rw [show [F7] ++ L5550 ++ [F3] = L9726 from rfl, show [F7] ++ L5550 = L5546 from rfl,
    show L5550 ++ [F3] = L9724 from rfl] at h
  rw [i5769 hinj, i3136 hinj, i5768 hinj, i3139 hinj] at h
  linarith

theorem row2004 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8266 + (1 : ℝ) * HLm Γ 5 L9727 + (-1 : ℝ) * HLm Γ 5 L9729 + (-1 : ℝ) * HLm Γ 5 L8264 := by
  have h := HLm_submod hΓ [F210] L8265 [F34]
  rw [show [F210] ++ L8265 ++ [F34] = L9730 from rfl, show [F210] ++ L8265 = L8267 from rfl,
    show L8265 ++ [F34] = L9728 from rfl] at h
  rw [i5771 hinj, i4871 hinj, i5770 hinj, i4870 hinj] at h
  linarith

theorem row2005 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1278 + (1 : ℝ) * HLm Γ 5 L9503 + (-1 : ℝ) * HLm Γ 5 L4252 + (-1 : ℝ) * HLm Γ 5 L5562 := by
  have h := HLm_submod hΓ [F1] L5563 [F210]
  rw [show [F1] ++ L5563 ++ [F210] = L9732 from rfl, show [F1] ++ L5563 = L5558 from rfl,
    show L5563 ++ [F210] = L9731 from rfl] at h
  rw [i5773 hinj, i3144 hinj, i5772 hinj, i3147 hinj] at h
  linarith

theorem row2006 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8294 + (1 : ℝ) * HLm Γ 5 L9734 + (-1 : ℝ) * HLm Γ 5 L9736 + (-1 : ℝ) * HLm Γ 5 L8292 := by
  have h := HLm_submod hΓ [F7] L9738 [F2]
  rw [show [F7] ++ L9738 ++ [F2] = L9737 from rfl, show [F7] ++ L9738 = L9733 from rfl,
    show L9738 ++ [F2] = L9735 from rfl] at h
  rw [i5776 hinj, i5774 hinj, i5775 hinj, i5777 hinj] at h
  linarith

theorem row2007 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4503 + (1 : ℝ) * HLm Γ 5 L9739 + (-1 : ℝ) * HLm Γ 5 L4949 + (-1 : ℝ) * HLm Γ 5 L8285 := by
  have h := HLm_submod hΓ [F7] L8286 [F3]
  rw [show [F7] ++ L8286 ++ [F3] = L9741 from rfl, show [F7] ++ L8286 = L8287 from rfl,
    show L8286 ++ [F3] = L9740 from rfl] at h
  rw [i5779 hinj, i4883 hinj, i5778 hinj, i4882 hinj] at h
  linarith

theorem row2008 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8300 + (1 : ℝ) * HLm Γ 5 L9743 + (-1 : ℝ) * HLm Γ 5 L9745 + (-1 : ℝ) * HLm Γ 5 L8298 := by
  have h := HLm_submod hΓ [F7] L9747 [F3]
  rw [show [F7] ++ L9747 ++ [F3] = L9746 from rfl, show [F7] ++ L9747 = L9742 from rfl,
    show L9747 ++ [F3] = L9744 from rfl] at h
  rw [i5782 hinj, i5780 hinj, i5781 hinj, i5783 hinj] at h
  linarith

theorem row2009 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8995 + (1 : ℝ) * HLm Γ 5 L8324 + (-1 : ℝ) * HLm Γ 5 L6352 + (-1 : ℝ) * HLm Γ 5 L8322 := by
  have h := HLm_submod hΓ [F7] L9751 [F1]
  rw [show [F7] ++ L9751 ++ [F1] = L9750 from rfl, show [F7] ++ L9751 = L9748 from rfl,
    show L9751 ++ [F1] = L9749 from rfl] at h
  rw [i5786 hinj, i5784 hinj, i5785 hinj, i5787 hinj] at h
  linarith

theorem row2010 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8995 + (1 : ℝ) * HLm Γ 5 L5502 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L8322 := by
  have h := HLm_submod hΓ [F7] L9751 [F4]
  rw [show [F7] ++ L9751 ++ [F4] = L9753 from rfl, show [F7] ++ L9751 = L9748 from rfl,
    show L9751 ++ [F4] = L9752 from rfl] at h
  rw [i5789 hinj, i5784 hinj, i5788 hinj, i5787 hinj] at h
  linarith

theorem row2011 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8317 + (1 : ℝ) * HLm Γ 5 L8755 + (-1 : ℝ) * HLm Γ 5 L6352 + (-1 : ℝ) * HLm Γ 5 L8315 := by
  have h := HLm_submod hΓ [F7] L9757 [F1]
  rw [show [F7] ++ L9757 ++ [F1] = L9756 from rfl, show [F7] ++ L9757 = L9754 from rfl,
    show L9757 ++ [F1] = L9755 from rfl] at h
  rw [i5792 hinj, i5790 hinj, i5791 hinj, i5793 hinj] at h
  linarith

theorem row2012 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1745 + (1 : ℝ) * HLm Γ 5 L4895 + (-1 : ℝ) * HLm Γ 5 L6174 + (-1 : ℝ) * HLm Γ 5 L8332 := by
  have h := HLm_submod hΓ [F16] L9761 [F228]
  rw [show [F16] ++ L9761 ++ [F228] = L9760 from rfl, show [F16] ++ L9761 = L9758 from rfl,
    show L9761 ++ [F228] = L9759 from rfl] at h
  rw [i5796 hinj, i5794 hinj, i5795 hinj, i5797 hinj] at h
  linarith

theorem row2013 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8414 + (1 : ℝ) * HLm Γ 5 L9763 + (-1 : ℝ) * HLm Γ 5 L9765 + (-1 : ℝ) * HLm Γ 5 L8345 := by
  have h := HLm_submod hΓ [F0] L9767 [F16]
  rw [show [F0] ++ L9767 ++ [F16] = L9766 from rfl, show [F0] ++ L9767 = L9762 from rfl,
    show L9767 ++ [F16] = L9764 from rfl] at h
  rw [i5800 hinj, i5798 hinj, i5799 hinj, i5801 hinj] at h
  linarith

theorem row2014 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9768 + (1 : ℝ) * HLm Γ 5 L9770 + (-1 : ℝ) * HLm Γ 5 L9772 + (-1 : ℝ) * HLm Γ 5 L8351 := by
  have h := HLm_submod hΓ [F67] L9774 [F210]
  rw [show [F67] ++ L9774 ++ [F210] = L9773 from rfl, show [F67] ++ L9774 = L9769 from rfl,
    show L9774 ++ [F210] = L9771 from rfl] at h
  rw [i5804 hinj, i5802 hinj, i5803 hinj, i5805 hinj] at h
  linarith

theorem row2015 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9141 + (1 : ℝ) * HLm Γ 5 L8354 + (-1 : ℝ) * HLm Γ 5 L9772 + (-1 : ℝ) * HLm Γ 5 L9137 := by
  have h := HLm_submod hΓ [F67] L9138 [F27]
  rw [show [F67] ++ L9138 ++ [F27] = L9777 from rfl, show [F67] ++ L9138 = L9775 from rfl,
    show L9138 ++ [F27] = L9776 from rfl] at h
  rw [i5808 hinj, i5806 hinj, i5807 hinj, i5402 hinj] at h
  linarith

theorem row2016 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9778 + (1 : ℝ) * HLm Γ 5 L8372 + (-1 : ℝ) * HLm Γ 5 L9781 + (-1 : ℝ) * HLm Γ 5 L2433 := by
  have h := HLm_submod hΓ [F9] L9783 [F210]
  rw [show [F9] ++ L9783 ++ [F210] = L9782 from rfl, show [F9] ++ L9783 = L9779 from rfl,
    show L9783 ++ [F210] = L9780 from rfl] at h
  rw [i5811 hinj, i5809 hinj, i5810 hinj, i5812 hinj] at h
  linarith

theorem row2017 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1278 + (1 : ℝ) * HLm Γ 5 L8361 + (-1 : ℝ) * HLm Γ 5 L4252 + (-1 : ℝ) * HLm Γ 5 L8359 := by
  have h := HLm_submod hΓ [F0] L8360 [F210]
  rw [show [F0] ++ L8360 ++ [F210] = L9786 from rfl, show [F0] ++ L8360 = L9784 from rfl,
    show L8360 ++ [F210] = L9785 from rfl] at h
  rw [i5815 hinj, i5813 hinj, i5814 hinj, i4925 hinj] at h
  linarith

theorem row2018 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4630 + (1 : ℝ) * HLm Γ 5 L9788 + (-1 : ℝ) * HLm Γ 5 L5912 + (-1 : ℝ) * HLm Γ 5 L9791 := by
  have h := HLm_submod hΓ [F2] L9792 [F211]
  rw [show [F2] ++ L9792 ++ [F211] = L9790 from rfl, show [F2] ++ L9792 = L9787 from rfl,
    show L9792 ++ [F211] = L9789 from rfl] at h
  rw [i5818 hinj, i5816 hinj, i5817 hinj, i5819 hinj] at h
  linarith

theorem row2019 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L8410 + (-1 : ℝ) * HLm Γ 5 L4558 + (-1 : ℝ) * HLm Γ 5 L1376 := by
  have h := HLm_submod hΓ [F0] L1840 [F217]
  rw [show [F0] ++ L1840 ++ [F217] = L9794 from rfl, show [F0] ++ L1840 = L1837 from rfl,
    show L1840 ++ [F217] = L9793 from rfl] at h
  rw [i5821 hinj, i984 hinj, i5820 hinj, i987 hinj] at h
  linarith

theorem row2020 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L9796 + (-1 : ℝ) * HLm Γ 5 L4558 + (-1 : ℝ) * HLm Γ 5 L2561 := by
  have h := HLm_submod hΓ [F0] L9799 [F219]
  rw [show [F0] ++ L9799 ++ [F219] = L9798 from rfl, show [F0] ++ L9799 = L9795 from rfl,
    show L9799 ++ [F219] = L9797 from rfl] at h
  rw [i5824 hinj, i5822 hinj, i5823 hinj, i5825 hinj] at h
  linarith

theorem row2021 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L1731 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L9801 := by
  have h := HLm_submod hΓ [F0] L9802 [F67]
  rw [show [F0] ++ L9802 ++ [F67] = L6510 from rfl, show [F0] ++ L9802 = L9800 from rfl,
    show L9802 ++ [F67] = L6513 from rfl] at h
  rw [i3798 hinj, i5826 hinj, i3801 hinj, i5827 hinj] at h
  linarith

theorem row2022 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L8404 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L8402 := by
  have h := HLm_submod hΓ [F0] L8403 [F67]
  rw [show [F0] ++ L8403 ++ [F67] = L9805 from rfl, show [F0] ++ L8403 = L9803 from rfl,
    show L8403 ++ [F67] = L9804 from rfl] at h
  rw [i5830 hinj, i5828 hinj, i5829 hinj, i4952 hinj] at h
  linarith

theorem row2023 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L9807 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L8823 := by
  have h := HLm_submod hΓ [F0] L9810 [F67]
  rw [show [F0] ++ L9810 ++ [F67] = L9809 from rfl, show [F0] ++ L9810 = L9806 from rfl,
    show L9810 ++ [F67] = L9808 from rfl] at h
  rw [i5833 hinj, i5831 hinj, i5832 hinj, i5834 hinj] at h
  linarith

theorem row2024 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1719 + (1 : ℝ) * HLm Γ 5 L4210 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L9814 := by
  have h := HLm_submod hΓ [F1] L9815 [F0]
  rw [show [F1] ++ L9815 ++ [F0] = L9813 from rfl, show [F1] ++ L9815 = L9811 from rfl,
    show L9815 ++ [F0] = L9812 from rfl] at h
  rw [i5837 hinj, i5835 hinj, i5836 hinj, i5838 hinj] at h
  linarith

theorem row2025 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1842 + (1 : ℝ) * HLm Γ 5 L9817 + (-1 : ℝ) * HLm Γ 5 L9819 + (-1 : ℝ) * HLm Γ 5 L9814 := by
  have h := HLm_submod hΓ [F51] L9815 [F210]
  rw [show [F51] ++ L9815 ++ [F210] = L9820 from rfl, show [F51] ++ L9815 = L9816 from rfl,
    show L9815 ++ [F210] = L9818 from rfl] at h
  rw [i5841 hinj, i5839 hinj, i5840 hinj, i5838 hinj] at h
  linarith

theorem row2026 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4579 + (1 : ℝ) * HLm Γ 5 L9822 + (-1 : ℝ) * HLm Γ 5 L5889 + (-1 : ℝ) * HLm Γ 5 L8694 := by
  have h := HLm_submod hΓ [F0] L9825 [F16]
  rw [show [F0] ++ L9825 ++ [F16] = L9824 from rfl, show [F0] ++ L9825 = L9821 from rfl,
    show L9825 ++ [F16] = L9823 from rfl] at h
  rw [i5844 hinj, i5842 hinj, i5843 hinj, i5845 hinj] at h
  linarith

theorem row2027 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L8459 + (-1 : ℝ) * HLm Γ 5 L4558 + (-1 : ℝ) * HLm Γ 5 L8455 := by
  have h := HLm_submod hΓ [F0] L9829 [F218]
  rw [show [F0] ++ L9829 ++ [F218] = L9828 from rfl, show [F0] ++ L9829 = L9826 from rfl,
    show L9829 ++ [F218] = L9827 from rfl] at h
  rw [i5848 hinj, i5846 hinj, i5847 hinj, i5849 hinj] at h
  linarith

theorem row2028 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1894 + (1 : ℝ) * HLm Γ 5 L9831 + (-1 : ℝ) * HLm Γ 5 L6352 + (-1 : ℝ) * HLm Γ 5 L9834 := by
  have h := HLm_submod hΓ [F0] L9835 [F210]
  rw [show [F0] ++ L9835 ++ [F210] = L9833 from rfl, show [F0] ++ L9835 = L9830 from rfl,
    show L9835 ++ [F210] = L9832 from rfl] at h
  rw [i5852 hinj, i5850 hinj, i5851 hinj, i5853 hinj] at h
  linarith

theorem row2029 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9836 + (1 : ℝ) * HLm Γ 5 L9259 + (-1 : ℝ) * HLm Γ 5 L9839 + (-1 : ℝ) * HLm Γ 5 L9841 := by
  have h := HLm_submod hΓ [F52] L9842 [F210]
  rw [show [F52] ++ L9842 ++ [F210] = L9840 from rfl, show [F52] ++ L9842 = L9837 from rfl,
    show L9842 ++ [F210] = L9838 from rfl] at h
  rw [i5856 hinj, i5854 hinj, i5855 hinj, i5857 hinj] at h
  linarith

theorem row2030 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9348 + (1 : ℝ) * HLm Γ 5 L9844 + (-1 : ℝ) * HLm Γ 5 L9846 + (-1 : ℝ) * HLm Γ 5 L7439 := by
  have h := HLm_submod hΓ [F210] L9848 [F33]
  rw [show [F210] ++ L9848 ++ [F33] = L9847 from rfl, show [F210] ++ L9848 = L9843 from rfl,
    show L9848 ++ [F33] = L9845 from rfl] at h
  rw [i5860 hinj, i5858 hinj, i5859 hinj, i5861 hinj] at h
  linarith

theorem row2031 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9849 + (1 : ℝ) * HLm Γ 5 L9851 + (-1 : ℝ) * HLm Γ 5 L9853 + (-1 : ℝ) * HLm Γ 5 L9855 := by
  have h := HLm_submod hΓ [F47] L9856 [F210]
  rw [show [F47] ++ L9856 ++ [F210] = L9854 from rfl, show [F47] ++ L9856 = L9850 from rfl,
    show L9856 ++ [F210] = L9852 from rfl] at h
  rw [i5864 hinj, i5862 hinj, i5863 hinj, i5865 hinj] at h
  linarith

theorem row2032 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1564 + (1 : ℝ) * HLm Γ 5 L9858 + (-1 : ℝ) * HLm Γ 5 L9736 + (-1 : ℝ) * HLm Γ 5 L9861 := by
  have h := HLm_submod hΓ [F0] L9862 [F218]
  rw [show [F0] ++ L9862 ++ [F218] = L9860 from rfl, show [F0] ++ L9862 = L9857 from rfl,
    show L9862 ++ [F218] = L9859 from rfl] at h
  rw [i5868 hinj, i5866 hinj, i5867 hinj, i5869 hinj] at h
  linarith

theorem row2033 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5709 + (1 : ℝ) * HLm Γ 5 L9863 + (-1 : ℝ) * HLm Γ 5 L9865 + (-1 : ℝ) * HLm Γ 5 L5715 := by
  have h := HLm_submod hΓ [F210] L5716 [F36]
  rw [show [F210] ++ L5716 ++ [F36] = L9866 from rfl, show [F210] ++ L5716 = L5710 from rfl,
    show L5716 ++ [F36] = L9864 from rfl] at h
  rw [i5871 hinj, i3244 hinj, i5870 hinj, i3247 hinj] at h
  linarith

theorem row2034 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L8430 + (-1 : ℝ) * HLm Γ 5 L4558 + (-1 : ℝ) * HLm Γ 5 L8427 := by
  have h := HLm_submod hΓ [F0] L9870 [F218]
  rw [show [F0] ++ L9870 ++ [F218] = L9869 from rfl, show [F0] ++ L9870 = L9867 from rfl,
    show L9870 ++ [F218] = L9868 from rfl] at h
  rw [i5874 hinj, i5872 hinj, i5873 hinj, i5875 hinj] at h
  linarith

theorem row2035 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4448 + (1 : ℝ) * HLm Γ 5 L8430 + (-1 : ℝ) * HLm Γ 5 L5724 + (-1 : ℝ) * HLm Γ 5 L4174 := by
  have h := HLm_submod hΓ [F67] L8429 [F86]
  rw [show [F67] ++ L8429 ++ [F86] = L9873 from rfl, show [F67] ++ L8429 = L9871 from rfl,
    show L8429 ++ [F86] = L9872 from rfl] at h
  rw [i5878 hinj, i5876 hinj, i5877 hinj, i4968 hinj] at h
  linarith

theorem row2036 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9874 + (1 : ℝ) * HLm Γ 5 L8436 + (-1 : ℝ) * HLm Γ 5 L9877 + (-1 : ℝ) * HLm Γ 5 L8434 := by
  have h := HLm_submod hΓ [F23] L8435 [F210]
  rw [show [F23] ++ L8435 ++ [F210] = L9878 from rfl, show [F23] ++ L8435 = L9875 from rfl,
    show L8435 ++ [F210] = L9876 from rfl] at h
  rw [i5881 hinj, i5879 hinj, i5880 hinj, i4971 hinj] at h
  linarith

theorem row2037 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9879 + (1 : ℝ) * HLm Γ 5 L9881 + (-1 : ℝ) * HLm Γ 5 L9883 + (-1 : ℝ) * HLm Γ 5 L8615 := by
  have h := HLm_submod hΓ [F210] L9885 [F6]
  rw [show [F210] ++ L9885 ++ [F6] = L9884 from rfl, show [F210] ++ L9885 = L9880 from rfl,
    show L9885 ++ [F6] = L9882 from rfl] at h
  rw [i5884 hinj, i5882 hinj, i5883 hinj, i5885 hinj] at h
  linarith

theorem row2038 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9886 + (1 : ℝ) * HLm Γ 5 L8482 + (-1 : ℝ) * HLm Γ 5 L9889 + (-1 : ℝ) * HLm Γ 5 L9891 := by
  have h := HLm_submod hΓ [F0] L9892 [F6]
  rw [show [F0] ++ L9892 ++ [F6] = L9890 from rfl, show [F0] ++ L9892 = L9887 from rfl,
    show L9892 ++ [F6] = L9888 from rfl] at h
  rw [i5888 hinj, i5886 hinj, i5887 hinj, i5889 hinj] at h
  linarith

theorem row2039 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8896 + (1 : ℝ) * HLm Γ 5 L9894 + (-1 : ℝ) * HLm Γ 5 L9889 + (-1 : ℝ) * HLm Γ 5 L8479 := by
  have h := HLm_submod hΓ [F0] L9897 [F210]
  rw [show [F0] ++ L9897 ++ [F210] = L9896 from rfl, show [F0] ++ L9897 = L9893 from rfl,
    show L9897 ++ [F210] = L9895 from rfl] at h
  rw [i5892 hinj, i5890 hinj, i5891 hinj, i5893 hinj] at h
  linarith

theorem row2040 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2683 + (1 : ℝ) * HLm Γ 5 L9898 + (-1 : ℝ) * HLm Γ 5 L9900 + (-1 : ℝ) * HLm Γ 5 L8451 := by
  have h := HLm_submod hΓ [F0] L8452 [F214]
  rw [show [F0] ++ L8452 ++ [F214] = L9901 from rfl, show [F0] ++ L8452 = L8453 from rfl,
    show L8452 ++ [F214] = L9899 from rfl] at h
  rw [i5895 hinj, i4984 hinj, i5894 hinj, i4983 hinj] at h
  linarith

theorem row2041 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9902 + (1 : ℝ) * HLm Γ 5 L9904 + (-1 : ℝ) * HLm Γ 5 L9906 + (-1 : ℝ) * HLm Γ 5 L8457 := by
  have h := HLm_submod hΓ [F0] L8458 [F43]
  rw [show [F0] ++ L8458 ++ [F43] = L9907 from rfl, show [F0] ++ L8458 = L9903 from rfl,
    show L8458 ++ [F43] = L9905 from rfl] at h
  rw [i5898 hinj, i5896 hinj, i5897 hinj, i4987 hinj] at h
  linarith

theorem row2042 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9908 + (1 : ℝ) * HLm Γ 5 L9910 + (-1 : ℝ) * HLm Γ 5 L9912 + (-1 : ℝ) * HLm Γ 5 L9914 := by
  have h := HLm_submod hΓ [F1] L9915 [F85]
  rw [show [F1] ++ L9915 ++ [F85] = L9913 from rfl, show [F1] ++ L9915 = L9909 from rfl,
    show L9915 ++ [F85] = L9911 from rfl] at h
  rw [i5901 hinj, i5899 hinj, i5900 hinj, i5902 hinj] at h
  linarith

theorem row2043 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8470 + (1 : ℝ) * HLm Γ 5 L9916 + (-1 : ℝ) * HLm Γ 5 L9918 + (-1 : ℝ) * HLm Γ 5 L8468 := by
  have h := HLm_submod hΓ [F0] L8469 [F217]
  rw [show [F0] ++ L8469 ++ [F217] = L9919 from rfl, show [F0] ++ L8469 = L8471 from rfl,
    show L8469 ++ [F217] = L9917 from rfl] at h
  rw [i5904 hinj, i4994 hinj, i5903 hinj, i4993 hinj] at h
  linarith

theorem row2044 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9920 + (1 : ℝ) * HLm Γ 5 L8477 + (-1 : ℝ) * HLm Γ 5 L9923 + (-1 : ℝ) * HLm Γ 5 L9925 := by
  have h := HLm_submod hΓ [F0] L9926 [F43]
  rw [show [F0] ++ L9926 ++ [F43] = L9924 from rfl, show [F0] ++ L9926 = L9921 from rfl,
    show L9926 ++ [F43] = L9922 from rfl] at h
  rw [i5907 hinj, i5905 hinj, i5906 hinj, i5908 hinj] at h
  linarith

theorem row2045 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1719 + (1 : ℝ) * HLm Γ 5 L9928 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L8475 := by
  have h := HLm_submod hΓ [F1] L9931 [F0]
  rw [show [F1] ++ L9931 ++ [F0] = L9930 from rfl, show [F1] ++ L9931 = L9927 from rfl,
    show L9931 ++ [F0] = L9929 from rfl] at h
  rw [i5911 hinj, i5909 hinj, i5910 hinj, i5912 hinj] at h
  linarith

theorem row2046 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L9933 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L9936 := by
  have h := HLm_submod hΓ [F0] L9937 [F210]
  rw [show [F0] ++ L9937 ++ [F210] = L9935 from rfl, show [F0] ++ L9937 = L9932 from rfl,
    show L9937 ++ [F210] = L9934 from rfl] at h
  rw [i5915 hinj, i5913 hinj, i5914 hinj, i5916 hinj] at h
  linarith

theorem row2047 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5739 + (1 : ℝ) * HLm Γ 5 L5735 + (-1 : ℝ) * HLm Γ 5 L5515 + (-1 : ℝ) * HLm Γ 5 L9941 := by
  have h := HLm_submod hΓ [F0] L9942 [F3]
  rw [show [F0] ++ L9942 ++ [F3] = L9940 from rfl, show [F0] ++ L9942 = L9938 from rfl,
    show L9942 ++ [F3] = L9939 from rfl] at h
  rw [i5919 hinj, i5917 hinj, i5918 hinj, i5920 hinj] at h
  linarith

theorem row2048 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5739 + (1 : ℝ) * HLm Γ 5 L9944 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L9947 := by
  have h := HLm_submod hΓ [F0] L9948 [F4]
  rw [show [F0] ++ L9948 ++ [F4] = L9946 from rfl, show [F0] ++ L9948 = L9943 from rfl,
    show L9948 ++ [F4] = L9945 from rfl] at h
  rw [i5923 hinj, i5921 hinj, i5922 hinj, i5924 hinj] at h
  linarith

theorem row2049 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6360 + (1 : ℝ) * HLm Γ 5 L9950 + (-1 : ℝ) * HLm Γ 5 L5461 + (-1 : ℝ) * HLm Γ 5 L9953 := by
  have h := HLm_submod hΓ [F0] L9954 [F3]
  rw [show [F0] ++ L9954 ++ [F3] = L9952 from rfl, show [F0] ++ L9954 = L9949 from rfl,
    show L9954 ++ [F3] = L9951 from rfl] at h
  rw [i5927 hinj, i5925 hinj, i5926 hinj, i5928 hinj] at h
  linarith

theorem row2050 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5739 + (1 : ℝ) * HLm Γ 5 L9956 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L9959 := by
  have h := HLm_submod hΓ [F0] L9960 [F4]
  rw [show [F0] ++ L9960 ++ [F4] = L9958 from rfl, show [F0] ++ L9960 = L9955 from rfl,
    show L9960 ++ [F4] = L9957 from rfl] at h
  rw [i5931 hinj, i5929 hinj, i5930 hinj, i5932 hinj] at h
  linarith

theorem row2051 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9961 + (1 : ℝ) * HLm Γ 5 L9963 + (-1 : ℝ) * HLm Γ 5 L9965 + (-1 : ℝ) * HLm Γ 5 L9967 := by
  have h := HLm_submod hΓ [F0] L9968 [F36]
  rw [show [F0] ++ L9968 ++ [F36] = L9966 from rfl, show [F0] ++ L9968 = L9962 from rfl,
    show L9968 ++ [F36] = L9964 from rfl] at h
  rw [i5935 hinj, i5933 hinj, i5934 hinj, i5936 hinj] at h
  linarith

theorem row2052 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8225 + (1 : ℝ) * HLm Γ 5 L9281 + (-1 : ℝ) * HLm Γ 5 L9971 + (-1 : ℝ) * HLm Γ 5 L9293 := by
  have h := HLm_submod hΓ [F0] L9973 [F82]
  rw [show [F0] ++ L9973 ++ [F82] = L9972 from rfl, show [F0] ++ L9973 = L9969 from rfl,
    show L9973 ++ [F82] = L9970 from rfl] at h
  rw [i5939 hinj, i5937 hinj, i5938 hinj, i5940 hinj] at h
  linarith

theorem row2053 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9974 + (1 : ℝ) * HLm Γ 5 L9976 + (-1 : ℝ) * HLm Γ 5 L9978 + (-1 : ℝ) * HLm Γ 5 L8517 := by
  have h := HLm_submod hΓ [F3] L8518 [F67]
  rw [show [F3] ++ L8518 ++ [F67] = L9979 from rfl, show [F3] ++ L8518 = L9975 from rfl,
    show L8518 ++ [F67] = L9977 from rfl] at h
  rw [i5943 hinj, i5941 hinj, i5942 hinj, i5024 hinj] at h
  linarith

theorem row2054 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3618 + (1 : ℝ) * HLm Γ 5 L5639 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L3359 := by
  have h := HLm_submod hΓ [F0] L9983 [F4]
  rw [show [F0] ++ L9983 ++ [F4] = L9982 from rfl, show [F0] ++ L9983 = L9980 from rfl,
    show L9983 ++ [F4] = L9981 from rfl] at h
  rw [i5946 hinj, i5944 hinj, i5945 hinj, i5947 hinj] at h
  linarith

theorem row2055 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1461 + (1 : ℝ) * HLm Γ 5 L9985 + (-1 : ℝ) * HLm Γ 5 L6718 + (-1 : ℝ) * HLm Γ 5 L8617 := by
  have h := HLm_submod hΓ [F0] L9988 [F219]
  rw [show [F0] ++ L9988 ++ [F219] = L9987 from rfl, show [F0] ++ L9988 = L9984 from rfl,
    show L9988 ++ [F219] = L9986 from rfl] at h
  rw [i5950 hinj, i5948 hinj, i5949 hinj, i5951 hinj] at h
  linarith

theorem row2056 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8539 + (1 : ℝ) * HLm Γ 5 L9989 + (-1 : ℝ) * HLm Γ 5 L5536 + (-1 : ℝ) * HLm Γ 5 L8537 := by
  have h := HLm_submod hΓ [F0] L8538 [F55]
  rw [show [F0] ++ L8538 ++ [F55] = L9991 from rfl, show [F0] ++ L8538 = L8540 from rfl,
    show L8538 ++ [F55] = L9990 from rfl] at h
  rw [i5953 hinj, i5040 hinj, i5952 hinj, i5039 hinj] at h
  linarith

theorem row2057 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4835 + (1 : ℝ) * HLm Γ 5 L8464 + (-1 : ℝ) * HLm Γ 5 L9993 + (-1 : ℝ) * HLm Γ 5 L8556 := by
  have h := HLm_submod hΓ [F0] L8557 [F3]
  rw [show [F0] ++ L8557 ++ [F3] = L9994 from rfl, show [F0] ++ L8557 = L8558 from rfl,
    show L8557 ++ [F3] = L9992 from rfl] at h
  rw [i5955 hinj, i5052 hinj, i5954 hinj, i5051 hinj] at h
  linarith

theorem row2058 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9995 + (1 : ℝ) * HLm Γ 5 L8578 + (-1 : ℝ) * HLm Γ 5 L9998 + (-1 : ℝ) * HLm Γ 5 L8576 := by
  have h := HLm_submod hΓ [F111] L10000 [F210]
  rw [show [F111] ++ L10000 ++ [F210] = L9999 from rfl, show [F111] ++ L10000 = L9996 from rfl,
    show L10000 ++ [F210] = L9997 from rfl] at h
  rw [i5958 hinj, i5956 hinj, i5957 hinj, i5959 hinj] at h
  linarith

theorem row2059 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8593 + (1 : ℝ) * HLm Γ 5 L10002 + (-1 : ℝ) * HLm Γ 5 L10004 + (-1 : ℝ) * HLm Γ 5 L8591 := by
  have h := HLm_submod hΓ [F0] L10006 [F1]
  rw [show [F0] ++ L10006 ++ [F1] = L10005 from rfl, show [F0] ++ L10006 = L10001 from rfl,
    show L10006 ++ [F1] = L10003 from rfl] at h
  rw [i5962 hinj, i5960 hinj, i5961 hinj, i5963 hinj] at h
  linarith

theorem row2060 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8586 + (1 : ℝ) * HLm Γ 5 L9817 + (-1 : ℝ) * HLm Γ 5 L10008 + (-1 : ℝ) * HLm Γ 5 L8584 := by
  have h := HLm_submod hΓ [F0] L8585 [F2]
  rw [show [F0] ++ L8585 ++ [F2] = L10009 from rfl, show [F0] ++ L8585 = L8587 from rfl,
    show L8585 ++ [F2] = L10007 from rfl] at h
  rw [i5965 hinj, i5069 hinj, i5964 hinj, i5068 hinj] at h
  linarith

theorem row2061 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8586 + (1 : ℝ) * HLm Γ 5 L5728 + (-1 : ℝ) * HLm Γ 5 L5730 + (-1 : ℝ) * HLm Γ 5 L8584 := by
  have h := HLm_submod hΓ [F0] L8585 [F3]
  rw [show [F0] ++ L8585 ++ [F3] = L10011 from rfl, show [F0] ++ L8585 = L8587 from rfl,
    show L8585 ++ [F3] = L10010 from rfl] at h
  rw [i5967 hinj, i5069 hinj, i5966 hinj, i5068 hinj] at h
  linarith

theorem row2062 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5762 + (1 : ℝ) * HLm Γ 5 L8610 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L8608 := by
  have h := HLm_submod hΓ [F0] L10015 [F108]
  rw [show [F0] ++ L10015 ++ [F108] = L10014 from rfl, show [F0] ++ L10015 = L10012 from rfl,
    show L10015 ++ [F108] = L10013 from rfl] at h
  rw [i5970 hinj, i5968 hinj, i5969 hinj, i5971 hinj] at h
  linarith

theorem row2063 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4455 + (1 : ℝ) * HLm Γ 5 L10017 + (-1 : ℝ) * HLm Γ 5 L5529 + (-1 : ℝ) * HLm Γ 5 L8604 := by
  have h := HLm_submod hΓ [F0] L10020 [F1]
  rw [show [F0] ++ L10020 ++ [F1] = L10019 from rfl, show [F0] ++ L10020 = L10016 from rfl,
    show L10020 ++ [F1] = L10018 from rfl] at h
  rw [i5974 hinj, i5972 hinj, i5973 hinj, i5975 hinj] at h
  linarith

theorem row2064 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9127 + (1 : ℝ) * HLm Γ 5 L7966 + (-1 : ℝ) * HLm Γ 5 L5381 + (-1 : ℝ) * HLm Γ 5 L9525 := by
  have h := HLm_submod hΓ [F1] L9526 [F0]
  rw [show [F1] ++ L9526 ++ [F0] = L10023 from rfl, show [F1] ++ L9526 = L10021 from rfl,
    show L9526 ++ [F0] = L10022 from rfl] at h
  rw [i5978 hinj, i5976 hinj, i5977 hinj, i5631 hinj] at h
  linarith

theorem row2065 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1719 + (1 : ℝ) * HLm Γ 5 L10025 + (-1 : ℝ) * HLm Γ 5 L5639 + (-1 : ℝ) * HLm Γ 5 L8625 := by
  have h := HLm_submod hΓ [F1] L10028 [F211]
  rw [show [F1] ++ L10028 ++ [F211] = L10027 from rfl, show [F1] ++ L10028 = L10024 from rfl,
    show L10028 ++ [F211] = L10026 from rfl] at h
  rw [i5981 hinj, i5979 hinj, i5980 hinj, i5982 hinj] at h
  linarith

theorem row2066 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8631 + (1 : ℝ) * HLm Γ 5 L10030 + (-1 : ℝ) * HLm Γ 5 L10032 + (-1 : ℝ) * HLm Γ 5 L8629 := by
  have h := HLm_submod hΓ [F0] L10034 [F2]
  rw [show [F0] ++ L10034 ++ [F2] = L10033 from rfl, show [F0] ++ L10034 = L10029 from rfl,
    show L10034 ++ [F2] = L10031 from rfl] at h
  rw [i5985 hinj, i5983 hinj, i5984 hinj, i5986 hinj] at h
  linarith

theorem row2067 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8636 + (1 : ℝ) * HLm Γ 5 L5931 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L8634 := by
  have h := HLm_submod hΓ [F0] L10038 [F4]
  rw [show [F0] ++ L10038 ++ [F4] = L10037 from rfl, show [F0] ++ L10038 = L10035 from rfl,
    show L10038 ++ [F4] = L10036 from rfl] at h
  rw [i5989 hinj, i5987 hinj, i5988 hinj, i5990 hinj] at h
  linarith

theorem row2068 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L8700 + (-1 : ℝ) * HLm Γ 5 L4558 + (-1 : ℝ) * HLm Γ 5 L3415 := by
  have h := HLm_submod hΓ [F0] L10042 [F217]
  rw [show [F0] ++ L10042 ++ [F217] = L10041 from rfl, show [F0] ++ L10042 = L10039 from rfl,
    show L10042 ++ [F217] = L10040 from rfl] at h
  rw [i5993 hinj, i5991 hinj, i5992 hinj, i5994 hinj] at h
  linarith

theorem row2069 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10043 + (1 : ℝ) * HLm Γ 5 L10045 + (-1 : ℝ) * HLm Γ 5 L10047 + (-1 : ℝ) * HLm Γ 5 L10049 := by
  have h := HLm_submod hΓ [F210] L10050 [F17]
  rw [show [F210] ++ L10050 ++ [F17] = L10048 from rfl, show [F210] ++ L10050 = L10044 from rfl,
    show L10050 ++ [F17] = L10046 from rfl] at h
  rw [i5997 hinj, i5995 hinj, i5996 hinj, i5998 hinj] at h
  linarith

theorem row2070 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8640 + (1 : ℝ) * HLm Γ 5 L5863 + (-1 : ℝ) * HLm Γ 5 L6617 + (-1 : ℝ) * HLm Γ 5 L8644 := by
  have h := HLm_submod hΓ [F16] L10054 [F211]
  rw [show [F16] ++ L10054 ++ [F211] = L10053 from rfl, show [F16] ++ L10054 = L10051 from rfl,
    show L10054 ++ [F211] = L10052 from rfl] at h
  rw [i6001 hinj, i5999 hinj, i6000 hinj, i6002 hinj] at h
  linarith

theorem row2071 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10055 + (1 : ℝ) * HLm Γ 5 L10057 + (-1 : ℝ) * HLm Γ 5 L10059 + (-1 : ℝ) * HLm Γ 5 L10061 := by
  have h := HLm_submod hΓ [F210] L10062 [F36]
  rw [show [F210] ++ L10062 ++ [F36] = L10060 from rfl, show [F210] ++ L10062 = L10056 from rfl,
    show L10062 ++ [F36] = L10058 from rfl] at h
  rw [i6005 hinj, i6003 hinj, i6004 hinj, i6006 hinj] at h
  linarith

theorem row2072 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10063 + (1 : ℝ) * HLm Γ 5 L10065 + (-1 : ℝ) * HLm Γ 5 L10067 + (-1 : ℝ) * HLm Γ 5 L10069 := by
  have h := HLm_submod hΓ [F210] L10070 [F33]
  rw [show [F210] ++ L10070 ++ [F33] = L10068 from rfl, show [F210] ++ L10070 = L10064 from rfl,
    show L10070 ++ [F33] = L10066 from rfl] at h
  rw [i6009 hinj, i6007 hinj, i6008 hinj, i6010 hinj] at h
  linarith

theorem row2073 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10071 + (1 : ℝ) * HLm Γ 5 L8654 + (-1 : ℝ) * HLm Γ 5 L10074 + (-1 : ℝ) * HLm Γ 5 L8652 := by
  have h := HLm_submod hΓ [F68] L10076 [F210]
  rw [show [F68] ++ L10076 ++ [F210] = L10075 from rfl, show [F68] ++ L10076 = L10072 from rfl,
    show L10076 ++ [F210] = L10073 from rfl] at h
  rw [i6013 hinj, i6011 hinj, i6012 hinj, i6014 hinj] at h
  linarith

theorem row2074 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10077 + (1 : ℝ) * HLm Γ 5 L10079 + (-1 : ℝ) * HLm Γ 5 L10081 + (-1 : ℝ) * HLm Γ 5 L4859 := by
  have h := HLm_submod hΓ [F210] L10083 [F36]
  rw [show [F210] ++ L10083 ++ [F36] = L10082 from rfl, show [F210] ++ L10083 = L10078 from rfl,
    show L10083 ++ [F36] = L10080 from rfl] at h
  rw [i6017 hinj, i6015 hinj, i6016 hinj, i6018 hinj] at h
  linarith

theorem row2075 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10084 + (1 : ℝ) * HLm Γ 5 L10086 + (-1 : ℝ) * HLm Γ 5 L10088 + (-1 : ℝ) * HLm Γ 5 L10090 := by
  have h := HLm_submod hΓ [F16] L10091 [F17]
  rw [show [F16] ++ L10091 ++ [F17] = L10089 from rfl, show [F16] ++ L10091 = L10085 from rfl,
    show L10091 ++ [F17] = L10087 from rfl] at h
  rw [i6021 hinj, i6019 hinj, i6020 hinj, i6022 hinj] at h
  linarith

theorem row2076 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8132 + (1 : ℝ) * HLm Γ 5 L8686 + (-1 : ℝ) * HLm Γ 5 L10094 + (-1 : ℝ) * HLm Γ 5 L8684 := by
  have h := HLm_submod hΓ [F0] L10096 [F210]
  rw [show [F0] ++ L10096 ++ [F210] = L10095 from rfl, show [F0] ++ L10096 = L10092 from rfl,
    show L10096 ++ [F210] = L10093 from rfl] at h
  rw [i6025 hinj, i6023 hinj, i6024 hinj, i6026 hinj] at h
  linarith

theorem row2077 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L8662 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L8660 := by
  have h := HLm_submod hΓ [F0] L10100 [F67]
  rw [show [F0] ++ L10100 ++ [F67] = L10099 from rfl, show [F0] ++ L10100 = L10097 from rfl,
    show L10100 ++ [F67] = L10098 from rfl] at h
  rw [i6029 hinj, i6027 hinj, i6028 hinj, i6030 hinj] at h
  linarith

theorem row2078 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10101 + (1 : ℝ) * HLm Γ 5 L5903 + (-1 : ℝ) * HLm Γ 5 L10103 + (-1 : ℝ) * HLm Γ 5 L5907 := by
  have h := HLm_submod hΓ [F9] L5908 [F210]
  rw [show [F9] ++ L5908 ++ [F210] = L10104 from rfl, show [F9] ++ L5908 = L10102 from rfl,
    show L5908 ++ [F210] = L5904 from rfl] at h
  rw [i6032 hinj, i6031 hinj, i3371 hinj, i3373 hinj] at h
  linarith

theorem row2079 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4558 + (1 : ℝ) * HLm Γ 5 L9326 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L8698 := by
  have h := HLm_submod hΓ [F1] L10108 [F67]
  rw [show [F1] ++ L10108 ++ [F67] = L10107 from rfl, show [F1] ++ L10108 = L10105 from rfl,
    show L10108 ++ [F67] = L10106 from rfl] at h
  rw [i6035 hinj, i6033 hinj, i6034 hinj, i6036 hinj] at h
  linarith

theorem row2080 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2813 + (1 : ℝ) * HLm Γ 5 L8670 + (-1 : ℝ) * HLm Γ 5 L10111 + (-1 : ℝ) * HLm Γ 5 L8668 := by
  have h := HLm_submod hΓ [F1] L8669 [F210]
  rw [show [F1] ++ L8669 ++ [F210] = L10112 from rfl, show [F1] ++ L8669 = L10109 from rfl,
    show L8669 ++ [F210] = L10110 from rfl] at h
  rw [i6039 hinj, i6037 hinj, i6038 hinj, i5116 hinj] at h
  linarith

theorem row2081 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10113 + (1 : ℝ) * HLm Γ 5 L10115 + (-1 : ℝ) * HLm Γ 5 L6089 + (-1 : ℝ) * HLm Γ 5 L8674 := by
  have h := HLm_submod hΓ [F1] L10118 [F9]
  rw [show [F1] ++ L10118 ++ [F9] = L10117 from rfl, show [F1] ++ L10118 = L10114 from rfl,
    show L10118 ++ [F9] = L10116 from rfl] at h
  rw [i6042 hinj, i6040 hinj, i6041 hinj, i6043 hinj] at h
  linarith

theorem row2082 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10119 + (1 : ℝ) * HLm Γ 5 L8678 + (-1 : ℝ) * HLm Γ 5 L10122 + (-1 : ℝ) * HLm Γ 5 L8676 := by
  have h := HLm_submod hΓ [F9] L10124 [F210]
  rw [show [F9] ++ L10124 ++ [F210] = L10123 from rfl, show [F9] ++ L10124 = L10120 from rfl,
    show L10124 ++ [F210] = L10121 from rfl] at h
  rw [i6046 hinj, i6044 hinj, i6045 hinj, i6047 hinj] at h
  linarith

theorem row2083 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10125 + (1 : ℝ) * HLm Γ 5 L10127 + (-1 : ℝ) * HLm Γ 5 L10129 + (-1 : ℝ) * HLm Γ 5 L10131 := by
  have h := HLm_submod hΓ [F210] L10132 [F36]
  rw [show [F210] ++ L10132 ++ [F36] = L10130 from rfl, show [F210] ++ L10132 = L10126 from rfl,
    show L10132 ++ [F36] = L10128 from rfl] at h
  rw [i6050 hinj, i6048 hinj, i6049 hinj, i6051 hinj] at h
  linarith

theorem row2084 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4358 + (1 : ℝ) * HLm Γ 5 L10134 + (-1 : ℝ) * HLm Γ 5 L5628 + (-1 : ℝ) * HLm Γ 5 L4599 := by
  have h := HLm_submod hΓ [F1] L10137 [F211]
  rw [show [F1] ++ L10137 ++ [F211] = L10136 from rfl, show [F1] ++ L10137 = L10133 from rfl,
    show L10137 ++ [F211] = L10135 from rfl] at h
  rw [i6054 hinj, i6052 hinj, i6053 hinj, i6055 hinj] at h
  linarith

theorem row2085 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10138 + (1 : ℝ) * HLm Γ 5 L10140 + (-1 : ℝ) * HLm Γ 5 L10142 + (-1 : ℝ) * HLm Γ 5 L8689 := by
  have h := HLm_submod hΓ [F51] L8690 [F210]
  rw [show [F51] ++ L8690 ++ [F210] = L10143 from rfl, show [F51] ++ L8690 = L10139 from rfl,
    show L8690 ++ [F210] = L10141 from rfl] at h
  rw [i6058 hinj, i6056 hinj, i6057 hinj, i5127 hinj] at h
  linarith

theorem row2086 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10144 + (1 : ℝ) * HLm Γ 5 L10146 + (-1 : ℝ) * HLm Γ 5 L10148 + (-1 : ℝ) * HLm Γ 5 L8759 := by
  have h := HLm_submod hΓ [F67] L10150 [F211]
  rw [show [F67] ++ L10150 ++ [F211] = L10149 from rfl, show [F67] ++ L10150 = L10145 from rfl,
    show L10150 ++ [F211] = L10147 from rfl] at h
  rw [i6061 hinj, i6059 hinj, i6060 hinj, i6062 hinj] at h
  linarith

theorem row2087 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10151 + (1 : ℝ) * HLm Γ 5 L10153 + (-1 : ℝ) * HLm Γ 5 L10155 + (-1 : ℝ) * HLm Γ 5 L3442 := by
  have h := HLm_submod hΓ [F210] L8997 [F34]
  rw [show [F210] ++ L8997 ++ [F34] = L10156 from rfl, show [F210] ++ L8997 = L10152 from rfl,
    show L8997 ++ [F34] = L10154 from rfl] at h
  rw [i6065 hinj, i6063 hinj, i6064 hinj, i5313 hinj] at h
  linarith

theorem row2088 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L10158 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L8717 := by
  have h := HLm_submod hΓ [F0] L10161 [F67]
  rw [show [F0] ++ L10161 ++ [F67] = L10160 from rfl, show [F0] ++ L10161 = L10157 from rfl,
    show L10161 ++ [F67] = L10159 from rfl] at h
  rw [i6068 hinj, i6066 hinj, i6067 hinj, i6069 hinj] at h
  linarith

theorem row2089 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L8747 + (-1 : ℝ) * HLm Γ 5 L4558 + (-1 : ℝ) * HLm Γ 5 L8743 := by
  have h := HLm_submod hΓ [F0] L10165 [F219]
  rw [show [F0] ++ L10165 ++ [F219] = L10164 from rfl, show [F0] ++ L10165 = L10162 from rfl,
    show L10165 ++ [F219] = L10163 from rfl] at h
  rw [i6072 hinj, i6070 hinj, i6071 hinj, i6073 hinj] at h
  linarith

theorem row2090 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L10167 + (-1 : ℝ) * HLm Γ 5 L4558 + (-1 : ℝ) * HLm Γ 5 L10170 := by
  have h := HLm_submod hΓ [F0] L10171 [F219]
  rw [show [F0] ++ L10171 ++ [F219] = L10169 from rfl, show [F0] ++ L10171 = L10166 from rfl,
    show L10171 ++ [F219] = L10168 from rfl] at h
  rw [i6076 hinj, i6074 hinj, i6075 hinj, i6077 hinj] at h
  linarith

theorem row2091 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L9171 + (-1 : ℝ) * HLm Γ 5 L4558 + (-1 : ℝ) * HLm Γ 5 L9167 := by
  have h := HLm_submod hΓ [F0] L9168 [F219]
  rw [show [F0] ++ L9168 ++ [F219] = L10173 from rfl, show [F0] ++ L9168 = L10172 from rfl,
    show L9168 ++ [F219] = L9172 from rfl] at h
  rw [i6079 hinj, i6078 hinj, i5421 hinj, i5419 hinj] at h
  linarith

theorem row2092 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10174 + (1 : ℝ) * HLm Γ 5 L10176 + (-1 : ℝ) * HLm Γ 5 L10178 + (-1 : ℝ) * HLm Γ 5 L10180 := by
  have h := HLm_submod hΓ [F210] L10181 [F34]
  rw [show [F210] ++ L10181 ++ [F34] = L10179 from rfl, show [F210] ++ L10181 = L10175 from rfl,
    show L10181 ++ [F34] = L10177 from rfl] at h
  rw [i6082 hinj, i6080 hinj, i6081 hinj, i6083 hinj] at h
  linarith

theorem row2093 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10182 + (1 : ℝ) * HLm Γ 5 L10184 + (-1 : ℝ) * HLm Γ 5 L10186 + (-1 : ℝ) * HLm Γ 5 L8727 := by
  have h := HLm_submod hΓ [F16] L8728 [F228]
  rw [show [F16] ++ L8728 ++ [F228] = L10187 from rfl, show [F16] ++ L8728 = L10183 from rfl,
    show L8728 ++ [F228] = L10185 from rfl] at h
  rw [i6086 hinj, i6084 hinj, i6085 hinj, i5149 hinj] at h
  linarith

theorem row2094 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L8768 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L8765 := by
  have h := HLm_submod hΓ [F0] L10191 [F67]
  rw [show [F0] ++ L10191 ++ [F67] = L10190 from rfl, show [F0] ++ L10191 = L10188 from rfl,
    show L10191 ++ [F67] = L10189 from rfl] at h
  rw [i6089 hinj, i6087 hinj, i6088 hinj, i6090 hinj] at h
  linarith

theorem row2095 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8734 + (1 : ℝ) * HLm Γ 5 L8739 + (-1 : ℝ) * HLm Γ 5 L10194 + (-1 : ℝ) * HLm Γ 5 L8010 := by
  have h := HLm_submod hΓ [F46] L10196 [F67]
  rw [show [F46] ++ L10196 ++ [F67] = L10195 from rfl, show [F46] ++ L10196 = L10192 from rfl,
    show L10196 ++ [F67] = L10193 from rfl] at h
  rw [i6093 hinj, i6091 hinj, i6092 hinj, i6094 hinj] at h
  linarith

theorem row2096 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10197 + (1 : ℝ) * HLm Γ 5 L9492 + (-1 : ℝ) * HLm Γ 5 L10200 + (-1 : ℝ) * HLm Γ 5 L9488 := by
  have h := HLm_submod hΓ [F44] L10202 [F210]
  rw [show [F44] ++ L10202 ++ [F210] = L10201 from rfl, show [F44] ++ L10202 = L10198 from rfl,
    show L10202 ++ [F210] = L10199 from rfl] at h
  rw [i6097 hinj, i6095 hinj, i6096 hinj, i6098 hinj] at h
  linarith

theorem row2097 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1257 + (1 : ℝ) * HLm Γ 5 L10204 + (-1 : ℝ) * HLm Γ 5 L6381 + (-1 : ℝ) * HLm Γ 5 L10207 := by
  have h := HLm_submod hΓ [F0] L10208 [F214]
  rw [show [F0] ++ L10208 ++ [F214] = L10206 from rfl, show [F0] ++ L10208 = L10203 from rfl,
    show L10208 ++ [F214] = L10205 from rfl] at h
  rw [i6101 hinj, i6099 hinj, i6100 hinj, i6102 hinj] at h
  linarith

theorem row2098 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8721 + (1 : ℝ) * HLm Γ 5 L9360 + (-1 : ℝ) * HLm Γ 5 L10211 + (-1 : ℝ) * HLm Γ 5 L8745 := by
  have h := HLm_submod hΓ [F111] L8746 [F67]
  rw [show [F111] ++ L8746 ++ [F67] = L10212 from rfl, show [F111] ++ L8746 = L10209 from rfl,
    show L8746 ++ [F67] = L10210 from rfl] at h
  rw [i6105 hinj, i6103 hinj, i6104 hinj, i5160 hinj] at h
  linarith

theorem row2099 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10213 + (1 : ℝ) * HLm Γ 5 L10215 + (-1 : ℝ) * HLm Γ 5 L10217 + (-1 : ℝ) * HLm Γ 5 L10219 := by
  have h := HLm_submod hΓ [F210] L10220 [F27]
  rw [show [F210] ++ L10220 ++ [F27] = L10218 from rfl, show [F210] ++ L10220 = L10214 from rfl,
    show L10220 ++ [F27] = L10216 from rfl] at h
  rw [i6108 hinj, i6106 hinj, i6107 hinj, i6109 hinj] at h
  linarith

end EntropyBounds.TwoSet.Certs.R7A5
