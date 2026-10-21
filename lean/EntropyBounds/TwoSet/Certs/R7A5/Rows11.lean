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

theorem row1650 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7846 + (1 : ℝ) * HLm Γ 5 L7848 + (-1 : ℝ) * HLm Γ 5 L7850 + (-1 : ℝ) * HLm Γ 5 L7852 := by
  have h := HLm_submod hΓ [F62] L7853 [F210]
  rw [show [F62] ++ L7853 ++ [F210] = L7851 from rfl, show [F62] ++ L7853 = L7847 from rfl,
    show L7853 ++ [F210] = L7849 from rfl] at h
  rw [i4634 hinj, i4632 hinj, i4633 hinj, i4635 hinj] at h
  linarith

theorem row1651 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7854 + (1 : ℝ) * HLm Γ 5 L7856 + (-1 : ℝ) * HLm Γ 5 L7858 + (-1 : ℝ) * HLm Γ 5 L3120 := by
  have h := HLm_submod hΓ [F51] L3121 [F210]
  rw [show [F51] ++ L3121 ++ [F210] = L7859 from rfl, show [F51] ++ L3121 = L7855 from rfl,
    show L3121 ++ [F210] = L7857 from rfl] at h
  rw [i4638 hinj, i4636 hinj, i4637 hinj, i1770 hinj] at h
  linarith

theorem row1652 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7860 + (1 : ℝ) * HLm Γ 5 L6937 + (-1 : ℝ) * HLm Γ 5 L7863 + (-1 : ℝ) * HLm Γ 5 L6935 := by
  have h := HLm_submod hΓ [F16] L6936 [F210]
  rw [show [F16] ++ L6936 ++ [F210] = L7864 from rfl, show [F16] ++ L6936 = L7861 from rfl,
    show L6936 ++ [F210] = L7862 from rfl] at h
  rw [i4641 hinj, i4639 hinj, i4640 hinj, i4123 hinj] at h
  linarith

theorem row1653 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7865 + (1 : ℝ) * HLm Γ 5 L7128 + (-1 : ℝ) * HLm Γ 5 L7867 + (-1 : ℝ) * HLm Γ 5 L7126 := by
  have h := HLm_submod hΓ [F210] L7126 [F85]
  rw [show [F210] ++ L7126 ++ [F85] = L7868 from rfl, show [F210] ++ L7126 = L7866 from rfl,
    show L7126 ++ [F85] = L7129 from rfl] at h
  rw [i4643 hinj, i4642 hinj, i4229 hinj] at h
  linarith

theorem row1654 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7869 + (1 : ℝ) * HLm Γ 5 L7871 + (-1 : ℝ) * HLm Γ 5 L7873 + (-1 : ℝ) * HLm Γ 5 L7126 := by
  have h := HLm_submod hΓ [F214] L7126 [F34]
  rw [show [F214] ++ L7126 ++ [F34] = L7874 from rfl, show [F214] ++ L7126 = L7870 from rfl,
    show L7126 ++ [F34] = L7872 from rfl] at h
  rw [i4646 hinj, i4644 hinj, i4645 hinj] at h
  linarith

theorem row1655 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4602 + (1 : ℝ) * HLm Γ 5 L5279 + (-1 : ℝ) * HLm Γ 5 L4599 + (-1 : ℝ) * HLm Γ 5 L7876 := by
  have h := HLm_submod hΓ [F2] L7877 [F27]
  rw [show [F2] ++ L7877 ++ [F27] = L4600 from rfl, show [F2] ++ L7877 = L4603 from rfl,
    show L7877 ++ [F27] = L7875 from rfl] at h
  rw [i2582 hinj, i2584 hinj, i4647 hinj, i4648 hinj] at h
  linarith

theorem row1656 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3968 + (1 : ℝ) * HLm Γ 5 L7878 + (-1 : ℝ) * HLm Γ 5 L7880 + (-1 : ℝ) * HLm Γ 5 L3974 := by
  have h := HLm_submod hΓ [F3] L3975 [F211]
  rw [show [F3] ++ L3975 ++ [F211] = L7881 from rfl, show [F3] ++ L3975 = L3969 from rfl,
    show L3975 ++ [F211] = L7879 from rfl] at h
  rw [i4650 hinj, i2215 hinj, i4649 hinj, i2218 hinj] at h
  linarith

theorem row1657 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7882 + (1 : ℝ) * HLm Γ 5 L6944 + (-1 : ℝ) * HLm Γ 5 L7885 + (-1 : ℝ) * HLm Γ 5 L6942 := by
  have h := HLm_submod hΓ [F44] L6943 [F210]
  rw [show [F44] ++ L6943 ++ [F210] = L7886 from rfl, show [F44] ++ L6943 = L7883 from rfl,
    show L6943 ++ [F210] = L7884 from rfl] at h
  rw [i4653 hinj, i4651 hinj, i4652 hinj, i4126 hinj] at h
  linarith

theorem row1658 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7595 + (1 : ℝ) * HLm Γ 5 L7888 + (-1 : ℝ) * HLm Γ 5 L7890 + (-1 : ℝ) * HLm Γ 5 L2853 := by
  have h := HLm_submod hΓ [F4] L2854 [F210]
  rw [show [F4] ++ L2854 ++ [F210] = L7891 from rfl, show [F4] ++ L2854 = L7887 from rfl,
    show L2854 ++ [F210] = L7889 from rfl] at h
  rw [i4656 hinj, i4654 hinj, i4655 hinj, i1634 hinj] at h
  linarith

theorem row1659 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7892 + (1 : ℝ) * HLm Γ 5 L7894 + (-1 : ℝ) * HLm Γ 5 L7896 + (-1 : ℝ) * HLm Γ 5 L423 := by
  have h := HLm_submod hΓ [F210] L3982 [F17]
  rw [show [F210] ++ L3982 ++ [F17] = L7897 from rfl, show [F210] ++ L3982 = L7893 from rfl,
    show L3982 ++ [F17] = L7895 from rfl] at h
  rw [i4659 hinj, i4657 hinj, i4658 hinj, i2222 hinj] at h
  linarith

theorem row1660 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7898 + (1 : ℝ) * HLm Γ 5 L7900 + (-1 : ℝ) * HLm Γ 5 L7902 + (-1 : ℝ) * HLm Γ 5 L423 := by
  have h := HLm_submod hΓ [F236] L3982 [F27]
  rw [show [F236] ++ L3982 ++ [F27] = L7903 from rfl, show [F236] ++ L3982 = L7899 from rfl,
    show L3982 ++ [F27] = L7901 from rfl] at h
  rw [i4662 hinj, i4660 hinj, i4661 hinj, i2222 hinj] at h
  linarith

theorem row1661 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7904 + (1 : ℝ) * HLm Γ 5 L7906 + (-1 : ℝ) * HLm Γ 5 L7908 + (-1 : ℝ) * HLm Γ 5 L3001 := by
  have h := HLm_submod hΓ [F3] L3002 [F211]
  rw [show [F3] ++ L3002 ++ [F211] = L7909 from rfl, show [F3] ++ L3002 = L7905 from rfl,
    show L3002 ++ [F211] = L7907 from rfl] at h
  rw [i4665 hinj, i4663 hinj, i4664 hinj, i1710 hinj] at h
  linarith

theorem row1662 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2904 + (1 : ℝ) * HLm Γ 5 L7910 + (-1 : ℝ) * HLm Γ 5 L7912 + (-1 : ℝ) * HLm Γ 5 L294 := by
  have h := HLm_submod hΓ [F9] L3047 [F236]
  rw [show [F9] ++ L3047 ++ [F236] = L7913 from rfl, show [F9] ++ L3047 = L4002 from rfl,
    show L3047 ++ [F236] = L7911 from rfl] at h
  rw [i4667 hinj, i2234 hinj, i4666 hinj, i1733 hinj] at h
  linarith

theorem row1663 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7914 + (1 : ℝ) * HLm Γ 5 L3048 + (-1 : ℝ) * HLm Γ 5 L7917 + (-1 : ℝ) * HLm Γ 5 L439 := by
  have h := HLm_submod hΓ [F1] L440 [F27]
  rw [show [F1] ++ L440 ++ [F27] = L7918 from rfl, show [F1] ++ L440 = L7915 from rfl,
    show L440 ++ [F27] = L7916 from rfl] at h
  rw [i4670 hinj, i4668 hinj, i4669 hinj, i180 hinj] at h
  linarith

theorem row1664 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7919 + (1 : ℝ) * HLm Γ 5 L7921 + (-1 : ℝ) * HLm Γ 5 L7923 + (-1 : ℝ) * HLm Γ 5 L7925 := by
  have h := HLm_submod hΓ [F211] L7926 [F55]
  rw [show [F211] ++ L7926 ++ [F55] = L7924 from rfl, show [F211] ++ L7926 = L7920 from rfl,
    show L7926 ++ [F55] = L7922 from rfl] at h
  rw [i4673 hinj, i4671 hinj, i4672 hinj, i4674 hinj] at h
  linarith

theorem row1665 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4354 + (1 : ℝ) * HLm Γ 5 L7928 + (-1 : ℝ) * HLm Γ 5 L4358 + (-1 : ℝ) * HLm Γ 5 L7931 := by
  have h := HLm_submod hΓ [F4] L7932 [F27]
  rw [show [F4] ++ L7932 ++ [F27] = L7930 from rfl, show [F4] ++ L7932 = L7927 from rfl,
    show L7932 ++ [F27] = L7929 from rfl] at h
  rw [i4677 hinj, i4675 hinj, i4676 hinj, i4678 hinj] at h
  linarith

theorem row1666 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7933 + (1 : ℝ) * HLm Γ 5 L3702 + (-1 : ℝ) * HLm Γ 5 L7936 + (-1 : ℝ) * HLm Γ 5 L3165 := by
  have h := HLm_submod hΓ [F7] L3165 [F3]
  rw [show [F7] ++ L3165 ++ [F3] = L7937 from rfl, show [F7] ++ L3165 = L7934 from rfl,
    show L3165 ++ [F3] = L7935 from rfl] at h
  rw [i4681 hinj, i4679 hinj, i4680 hinj] at h
  linarith

theorem row1667 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3616 + (1 : ℝ) * HLm Γ 5 L7142 + (-1 : ℝ) * HLm Γ 5 L5381 + (-1 : ℝ) * HLm Γ 5 L7141 := by
  have h := HLm_submod hΓ [F10] L7141 [F6]
  rw [show [F10] ++ L7141 ++ [F6] = L7939 from rfl, show [F10] ++ L7141 = L7938 from rfl,
    show L7141 ++ [F6] = L7142 from rfl] at h
  rw [i4683 hinj, i4682 hinj] at h
  linarith

theorem row1668 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7941 + (1 : ℝ) * HLm Γ 5 L7943 + (-1 : ℝ) * HLm Γ 5 L7945 + (-1 : ℝ) * HLm Γ 5 L7947 := by
  have h := HLm_submod hΓ [F3] L7948 [F45]
  rw [show [F3] ++ L7948 ++ [F45] = L7946 from rfl, show [F3] ++ L7948 = L7942 from rfl,
    show L7948 ++ [F45] = L7944 from rfl] at h
  rw [i4686 hinj, i4684 hinj, i4685 hinj, i4687 hinj] at h
  linarith

theorem row1669 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7949 + (1 : ℝ) * HLm Γ 5 L7951 + (-1 : ℝ) * HLm Γ 5 L7953 + (-1 : ℝ) * HLm Γ 5 L7015 := by
  have h := HLm_submod hΓ [F1] L7016 [F6]
  rw [show [F1] ++ L7016 ++ [F6] = L7954 from rfl, show [F1] ++ L7016 = L7950 from rfl,
    show L7016 ++ [F6] = L7952 from rfl] at h
  rw [i4690 hinj, i4688 hinj, i4689 hinj, i4165 hinj] at h
  linarith

theorem row1670 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3388 + (1 : ℝ) * HLm Γ 5 L7121 + (-1 : ℝ) * HLm Γ 5 L7955 + (-1 : ℝ) * HLm Γ 5 L4061 := by
  have h := HLm_submod hΓ [F7] L4061 [F55]
  rw [show [F7] ++ L4061 ++ [F55] = L7956 from rfl, show [F7] ++ L4061 = L4057 from rfl,
    show L4061 ++ [F55] = L7122 from rfl] at h
  rw [i4691 hinj, i2264 hinj, i4225 hinj] at h
  linarith

theorem row1671 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7957 + (1 : ℝ) * HLm Γ 5 L7959 + (-1 : ℝ) * HLm Γ 5 L7961 + (-1 : ℝ) * HLm Γ 5 L7963 := by
  have h := HLm_submod hΓ [F1] L7964 [F6]
  rw [show [F1] ++ L7964 ++ [F6] = L7962 from rfl, show [F1] ++ L7964 = L7958 from rfl,
    show L7964 ++ [F6] = L7960 from rfl] at h
  rw [i4694 hinj, i4692 hinj, i4693 hinj, i4695 hinj] at h
  linarith

theorem row1672 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3279 + (1 : ℝ) * HLm Γ 5 L4072 + (-1 : ℝ) * HLm Γ 5 L7966 + (-1 : ℝ) * HLm Γ 5 L4076 := by
  have h := HLm_submod hΓ [F10] L4077 [F219]
  rw [show [F10] ++ L4077 ++ [F219] = L7967 from rfl, show [F10] ++ L4077 = L7965 from rfl,
    show L4077 ++ [F219] = L4073 from rfl] at h
  rw [i4697 hinj, i4696 hinj, i2272 hinj, i2274 hinj] at h
  linarith

theorem row1673 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7968 + (1 : ℝ) * HLm Γ 5 L7970 + (-1 : ℝ) * HLm Γ 5 L7972 + (-1 : ℝ) * HLm Γ 5 L404 := by
  have h := HLm_submod hΓ [F210] L6962 [F6]
  rw [show [F210] ++ L6962 ++ [F6] = L7973 from rfl, show [F210] ++ L6962 = L7969 from rfl,
    show L6962 ++ [F6] = L7971 from rfl] at h
  rw [i4700 hinj, i4698 hinj, i4699 hinj, i4136 hinj] at h
  linarith

theorem row1674 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7974 + (1 : ℝ) * HLm Γ 5 L7976 + (-1 : ℝ) * HLm Γ 5 L7978 + (-1 : ℝ) * HLm Γ 5 L6965 := by
  have h := HLm_submod hΓ [F228] L6966 [F45]
  rw [show [F228] ++ L6966 ++ [F45] = L7979 from rfl, show [F228] ++ L6966 = L7975 from rfl,
    show L6966 ++ [F45] = L7977 from rfl] at h
  rw [i4703 hinj, i4701 hinj, i4702 hinj, i4138 hinj] at h
  linarith

theorem row1675 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7980 + (1 : ℝ) * HLm Γ 5 L7982 + (-1 : ℝ) * HLm Γ 5 L7984 + (-1 : ℝ) * HLm Γ 5 L6969 := by
  have h := HLm_submod hΓ [F7] L6970 [F217]
  rw [show [F7] ++ L6970 ++ [F217] = L7985 from rfl, show [F7] ++ L6970 = L7981 from rfl,
    show L6970 ++ [F217] = L7983 from rfl] at h
  rw [i4706 hinj, i4704 hinj, i4705 hinj, i4140 hinj] at h
  linarith

theorem row1676 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1003 + (1 : ℝ) * HLm Γ 5 L7090 + (-1 : ℝ) * HLm Γ 5 L1754 + (-1 : ℝ) * HLm Γ 5 L7088 := by
  have h := HLm_submod hΓ [F0] L7989 [F67]
  rw [show [F0] ++ L7989 ++ [F67] = L7988 from rfl, show [F0] ++ L7989 = L7986 from rfl,
    show L7989 ++ [F67] = L7987 from rfl] at h
  rw [i4709 hinj, i4707 hinj, i4708 hinj, i4710 hinj] at h
  linarith

theorem row1677 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7990 + (1 : ℝ) * HLm Γ 5 L220 + (-1 : ℝ) * HLm Γ 5 L7992 + (-1 : ℝ) * HLm Γ 5 L273 := by
  have h := HLm_submod hΓ [F51] L273 [F16]
  rw [show [F51] ++ L273 ++ [F16] = L7993 from rfl, show [F51] ++ L273 = L7991 from rfl,
    show L273 ++ [F16] = L1063 from rfl] at h
  rw [i4712 hinj, i4711 hinj, i499 hinj] at h
  linarith

theorem row1678 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L220 + (1 : ℝ) * HLm Γ 5 L7995 + (-1 : ℝ) * HLm Γ 5 L7997 + (-1 : ℝ) * HLm Γ 5 L273 := by
  have h := HLm_submod hΓ [F16] L273 [F214]
  rw [show [F16] ++ L273 ++ [F214] = L7998 from rfl, show [F16] ++ L273 = L7994 from rfl,
    show L273 ++ [F214] = L7996 from rfl] at h
  rw [i4715 hinj, i4713 hinj, i4714 hinj] at h
  linarith

theorem row1679 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7999 + (1 : ℝ) * HLm Γ 5 L6975 + (-1 : ℝ) * HLm Γ 5 L8001 + (-1 : ℝ) * HLm Γ 5 L273 := by
  have h := HLm_submod hΓ [F21] L273 [F210]
  rw [show [F21] ++ L273 ++ [F210] = L8002 from rfl, show [F21] ++ L273 = L8000 from rfl,
    show L273 ++ [F210] = L6975 from rfl] at h
  rw [i4717 hinj, i4716 hinj] at h
  linarith

theorem row1680 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8003 + (1 : ℝ) * HLm Γ 5 L7995 + (-1 : ℝ) * HLm Γ 5 L8005 + (-1 : ℝ) * HLm Γ 5 L273 := by
  have h := HLm_submod hΓ [F22] L273 [F214]
  rw [show [F22] ++ L273 ++ [F214] = L8006 from rfl, show [F22] ++ L273 = L8004 from rfl,
    show L273 ++ [F214] = L7996 from rfl] at h
  rw [i4719 hinj, i4718 hinj, i4714 hinj] at h
  linarith

theorem row1681 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6832 + (1 : ℝ) * HLm Γ 5 L8008 + (-1 : ℝ) * HLm Γ 5 L8010 + (-1 : ℝ) * HLm Γ 5 L6959 := by
  have h := HLm_submod hΓ [F51] L6959 [F16]
  rw [show [F51] ++ L6959 ++ [F16] = L8011 from rfl, show [F51] ++ L6959 = L8007 from rfl,
    show L6959 ++ [F16] = L8009 from rfl] at h
  rw [i4722 hinj, i4720 hinj, i4721 hinj] at h
  linarith

theorem row1682 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8012 + (1 : ℝ) * HLm Γ 5 L8014 + (-1 : ℝ) * HLm Γ 5 L8016 + (-1 : ℝ) * HLm Γ 5 L2149 := by
  have h := HLm_submod hΓ [F67] L8018 [F236]
  rw [show [F67] ++ L8018 ++ [F236] = L8017 from rfl, show [F67] ++ L8018 = L8013 from rfl,
    show L8018 ++ [F236] = L8015 from rfl] at h
  rw [i4725 hinj, i4723 hinj, i4724 hinj, i4726 hinj] at h
  linarith

theorem row1683 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2885 + (1 : ℝ) * HLm Γ 5 L3038 + (-1 : ℝ) * HLm Γ 5 L8019 + (-1 : ℝ) * HLm Γ 5 L452 := by
  have h := HLm_submod hΓ [F51] L452 [F210]
  rw [show [F51] ++ L452 ++ [F210] = L8019 from rfl, show [F51] ++ L452 = L2885 from rfl,
    show L452 ++ [F210] = L3038 from rfl] at h
  linarith

theorem row1684 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L454 + (1 : ℝ) * HLm Γ 5 L6952 + (-1 : ℝ) * HLm Γ 5 L8022 + (-1 : ℝ) * HLm Γ 5 L452 := by
  have h := HLm_submod hΓ [F16] L452 [F211]
  rw [show [F16] ++ L452 ++ [F211] = L8023 from rfl, show [F16] ++ L452 = L8020 from rfl,
    show L452 ++ [F211] = L8021 from rfl] at h
  rw [i4729 hinj, i4727 hinj, i4728 hinj] at h
  linarith

theorem row1685 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6857 + (1 : ℝ) * HLm Γ 5 L3788 + (-1 : ℝ) * HLm Γ 5 L8025 + (-1 : ℝ) * HLm Γ 5 L2857 := by
  have h := HLm_submod hΓ [F47] L2857 [F16]
  rw [show [F47] ++ L2857 ++ [F16] = L8026 from rfl, show [F47] ++ L2857 = L6857 from rfl,
    show L2857 ++ [F16] = L8024 from rfl] at h
  rw [i4731 hinj, i4730 hinj] at h
  linarith

theorem row1686 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8027 + (1 : ℝ) * HLm Γ 5 L3788 + (-1 : ℝ) * HLm Γ 5 L8029 + (-1 : ℝ) * HLm Γ 5 L2857 := by
  have h := HLm_submod hΓ [F44] L2857 [F16]
  rw [show [F44] ++ L2857 ++ [F16] = L8030 from rfl, show [F44] ++ L2857 = L8028 from rfl,
    show L2857 ++ [F16] = L8024 from rfl] at h
  rw [i4733 hinj, i4732 hinj, i4730 hinj] at h
  linarith

theorem row1687 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3434 + (1 : ℝ) * HLm Γ 5 L8031 + (-1 : ℝ) * HLm Γ 5 L8033 + (-1 : ℝ) * HLm Γ 5 L314 := by
  have h := HLm_submod hΓ [F2] L315 [F228]
  rw [show [F2] ++ L315 ++ [F228] = L8034 from rfl, show [F2] ++ L315 = L3435 from rfl,
    show L315 ++ [F228] = L8032 from rfl] at h
  rw [i4735 hinj, i1927 hinj, i4734 hinj, i122 hinj] at h
  linarith

theorem row1688 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L796 + (1 : ℝ) * HLm Γ 5 L8036 + (-1 : ℝ) * HLm Γ 5 L1606 + (-1 : ℝ) * HLm Γ 5 L314 := by
  have h := HLm_submod hΓ [F9] L315 [F25]
  rw [show [F9] ++ L315 ++ [F25] = L8038 from rfl, show [F9] ++ L315 = L8035 from rfl,
    show L315 ++ [F25] = L8037 from rfl] at h
  rw [i4738 hinj, i4736 hinj, i4737 hinj, i122 hinj] at h
  linarith

theorem row1689 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8039 + (1 : ℝ) * HLm Γ 5 L7113 + (-1 : ℝ) * HLm Γ 5 L8042 + (-1 : ℝ) * HLm Γ 5 L3043 := by
  have h := HLm_submod hΓ [F67] L3044 [F25]
  rw [show [F67] ++ L3044 ++ [F25] = L8043 from rfl, show [F67] ++ L3044 = L8040 from rfl,
    show L3044 ++ [F25] = L8041 from rfl] at h
  rw [i4741 hinj, i4739 hinj, i4740 hinj, i1731 hinj] at h
  linarith

theorem row1690 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2374 + (1 : ℝ) * HLm Γ 5 L7017 + (-1 : ℝ) * HLm Γ 5 L3656 + (-1 : ℝ) * HLm Γ 5 L2098 := by
  have h := HLm_submod hΓ [F12] L2099 [F228]
  rw [show [F12] ++ L2099 ++ [F228] = L8045 from rfl, show [F12] ++ L2099 = L2440 from rfl,
    show L2099 ++ [F228] = L8044 from rfl] at h
  rw [i4743 hinj, i1344 hinj, i4742 hinj, i1152 hinj] at h
  linarith

theorem row1691 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8046 + (1 : ℝ) * HLm Γ 5 L7013 + (-1 : ℝ) * HLm Γ 5 L8049 + (-1 : ℝ) * HLm Γ 5 L7011 := by
  have h := HLm_submod hΓ [F9] L7012 [F108]
  rw [show [F9] ++ L7012 ++ [F108] = L8050 from rfl, show [F9] ++ L7012 = L8047 from rfl,
    show L7012 ++ [F108] = L8048 from rfl] at h
  rw [i4746 hinj, i4744 hinj, i4745 hinj, i4163 hinj] at h
  linarith

theorem row1692 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1123 + (1 : ℝ) * HLm Γ 5 L7038 + (-1 : ℝ) * HLm Γ 5 L8053 + (-1 : ℝ) * HLm Γ 5 L7036 := by
  have h := HLm_submod hΓ [F1] L7037 [F210]
  rw [show [F1] ++ L7037 ++ [F210] = L8054 from rfl, show [F1] ++ L7037 = L8051 from rfl,
    show L7037 ++ [F210] = L8052 from rfl] at h
  rw [i4749 hinj, i4747 hinj, i4748 hinj, i4176 hinj] at h
  linarith

theorem row1693 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8055 + (1 : ℝ) * HLm Γ 5 L8057 + (-1 : ℝ) * HLm Γ 5 L8059 + (-1 : ℝ) * HLm Γ 5 L7036 := by
  have h := HLm_submod hΓ [F16] L7037 [F211]
  rw [show [F16] ++ L7037 ++ [F211] = L8060 from rfl, show [F16] ++ L7037 = L8056 from rfl,
    show L7037 ++ [F211] = L8058 from rfl] at h
  rw [i4752 hinj, i4750 hinj, i4751 hinj, i4176 hinj] at h
  linarith

theorem row1694 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7026 + (1 : ℝ) * HLm Γ 5 L8061 + (-1 : ℝ) * HLm Γ 5 L8063 + (-1 : ℝ) * HLm Γ 5 L7024 := by
  have h := HLm_submod hΓ [F12] L7025 [F67]
  rw [show [F12] ++ L7025 ++ [F67] = L8064 from rfl, show [F12] ++ L7025 = L7027 from rfl,
    show L7025 ++ [F67] = L8062 from rfl] at h
  rw [i4754 hinj, i4171 hinj, i4753 hinj, i4170 hinj] at h
  linarith

theorem row1695 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7304 + (1 : ℝ) * HLm Γ 5 L7044 + (-1 : ℝ) * HLm Γ 5 L8066 + (-1 : ℝ) * HLm Γ 5 L7042 := by
  have h := HLm_submod hΓ [F7] L7043 [F210]
  rw [show [F7] ++ L7043 ++ [F210] = L8067 from rfl, show [F7] ++ L7043 = L7305 from rfl,
    show L7043 ++ [F210] = L8065 from rfl] at h
  rw [i4756 hinj, i4330 hinj, i4755 hinj, i4179 hinj] at h
  linarith

theorem row1696 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8068 + (1 : ℝ) * HLm Γ 5 L8070 + (-1 : ℝ) * HLm Γ 5 L8072 + (-1 : ℝ) * HLm Γ 5 L3140 := by
  have h := HLm_submod hΓ [F210] L8074 [F90]
  rw [show [F210] ++ L8074 ++ [F90] = L8073 from rfl, show [F210] ++ L8074 = L8069 from rfl,
    show L8074 ++ [F90] = L8071 from rfl] at h
  rw [i4759 hinj, i4757 hinj, i4758 hinj, i4760 hinj] at h
  linarith

theorem row1697 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2409 + (1 : ℝ) * HLm Γ 5 L8076 + (-1 : ℝ) * HLm Γ 5 L3550 + (-1 : ℝ) * HLm Γ 5 L445 := by
  have h := HLm_submod hΓ [F9] L2138 [F210]
  rw [show [F9] ++ L2138 ++ [F210] = L8078 from rfl, show [F9] ++ L2138 = L8075 from rfl,
    show L2138 ++ [F210] = L8077 from rfl] at h
  rw [i4763 hinj, i4761 hinj, i4762 hinj, i1172 hinj] at h
  linarith

theorem row1698 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4170 + (1 : ℝ) * HLm Γ 5 L8079 + (-1 : ℝ) * HLm Γ 5 L8081 + (-1 : ℝ) * HLm Γ 5 L3215 := by
  have h := HLm_submod hΓ [F7] L4176 [F82]
  rw [show [F7] ++ L4176 ++ [F82] = L8082 from rfl, show [F7] ++ L4176 = L4171 from rfl,
    show L4176 ++ [F82] = L8080 from rfl] at h
  rw [i4765 hinj, i2329 hinj, i4764 hinj, i2332 hinj] at h
  linarith

theorem row1699 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8076 + (1 : ℝ) * HLm Γ 5 L7073 + (-1 : ℝ) * HLm Γ 5 L8085 + (-1 : ℝ) * HLm Γ 5 L3215 := by
  have h := HLm_submod hΓ [F210] L4176 [F43]
  rw [show [F210] ++ L4176 ++ [F43] = L8086 from rfl, show [F210] ++ L4176 = L8083 from rfl,
    show L4176 ++ [F43] = L8084 from rfl] at h
  rw [i4768 hinj, i4766 hinj, i4767 hinj, i2332 hinj] at h
  linarith

theorem row1700 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8087 + (1 : ℝ) * HLm Γ 5 L8089 + (-1 : ℝ) * HLm Γ 5 L8091 + (-1 : ℝ) * HLm Γ 5 L7119 := by
  have h := HLm_submod hΓ [F1] L8093 [F211]
  rw [show [F1] ++ L8093 ++ [F211] = L8092 from rfl, show [F1] ++ L8093 = L8088 from rfl,
    show L8093 ++ [F211] = L8090 from rfl] at h
  rw [i4771 hinj, i4769 hinj, i4770 hinj, i4772 hinj] at h
  linarith

theorem row1701 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3694 + (1 : ℝ) * HLm Γ 5 L8089 + (-1 : ℝ) * HLm Γ 5 L3696 + (-1 : ℝ) * HLm Γ 5 L7119 := by
  have h := HLm_submod hΓ [F3] L8093 [F211]
  rw [show [F3] ++ L8093 ++ [F211] = L8095 from rfl, show [F3] ++ L8093 = L8094 from rfl,
    show L8093 ++ [F211] = L8090 from rfl] at h
  rw [i4774 hinj, i4773 hinj, i4770 hinj, i4772 hinj] at h
  linarith

theorem row1702 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8096 + (1 : ℝ) * HLm Γ 5 L8098 + (-1 : ℝ) * HLm Γ 5 L8100 + (-1 : ℝ) * HLm Γ 5 L7119 := by
  have h := HLm_submod hΓ [F46] L8093 [F217]
  rw [show [F46] ++ L8093 ++ [F217] = L8101 from rfl, show [F46] ++ L8093 = L8097 from rfl,
    show L8093 ++ [F217] = L8099 from rfl] at h
  rw [i4777 hinj, i4775 hinj, i4776 hinj, i4772 hinj] at h
  linarith

theorem row1703 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7084 + (1 : ℝ) * HLm Γ 5 L8102 + (-1 : ℝ) * HLm Γ 5 L8104 + (-1 : ℝ) * HLm Γ 5 L7082 := by
  have h := HLm_submod hΓ [F7] L7083 [F82]
  rw [show [F7] ++ L7083 ++ [F82] = L8105 from rfl, show [F7] ++ L7083 = L7085 from rfl,
    show L7083 ++ [F82] = L8103 from rfl] at h
  rw [i4779 hinj, i4203 hinj, i4778 hinj, i4202 hinj] at h
  linarith

theorem row1704 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7139 + (1 : ℝ) * HLm Γ 5 L8107 + (-1 : ℝ) * HLm Γ 5 L8109 + (-1 : ℝ) * HLm Γ 5 L7082 := by
  have h := HLm_submod hΓ [F46] L7083 [F67]
  rw [show [F46] ++ L7083 ++ [F67] = L8110 from rfl, show [F46] ++ L7083 = L8106 from rfl,
    show L7083 ++ [F67] = L8108 from rfl] at h
  rw [i4782 hinj, i4780 hinj, i4781 hinj, i4202 hinj] at h
  linarith

theorem row1705 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7080 + (1 : ℝ) * HLm Γ 5 L8111 + (-1 : ℝ) * HLm Γ 5 L8113 + (-1 : ℝ) * HLm Γ 5 L7078 := by
  have h := HLm_submod hΓ [F0] L7079 [F82]
  rw [show [F0] ++ L7079 ++ [F82] = L8114 from rfl, show [F0] ++ L7079 = L7081 from rfl,
    show L7079 ++ [F82] = L8112 from rfl] at h
  rw [i4784 hinj, i4201 hinj, i4783 hinj, i4200 hinj] at h
  linarith

theorem row1706 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2873 + (1 : ℝ) * HLm Γ 5 L8115 + (-1 : ℝ) * HLm Γ 5 L8117 + (-1 : ℝ) * HLm Γ 5 L3182 := by
  have h := HLm_submod hΓ [F7] L3183 [F3]
  rw [show [F7] ++ L3183 ++ [F3] = L8118 from rfl, show [F7] ++ L3183 = L4185 from rfl,
    show L3183 ++ [F3] = L8116 from rfl] at h
  rw [i4786 hinj, i2337 hinj, i4785 hinj, i1800 hinj] at h
  linarith

theorem row1707 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8119 + (1 : ℝ) * HLm Γ 5 L8121 + (-1 : ℝ) * HLm Γ 5 L8123 + (-1 : ℝ) * HLm Γ 5 L555 := by
  have h := HLm_submod hΓ [F210] L1243 [F6]
  rw [show [F210] ++ L1243 ++ [F6] = L8124 from rfl, show [F210] ++ L1243 = L8120 from rfl,
    show L1243 ++ [F6] = L8122 from rfl] at h
  rw [i4789 hinj, i4787 hinj, i4788 hinj, i602 hinj] at h
  linarith

theorem row1708 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L851 + (1 : ℝ) * HLm Γ 5 L8125 + (-1 : ℝ) * HLm Γ 5 L1451 + (-1 : ℝ) * HLm Γ 5 L565 := by
  have h := HLm_submod hΓ [F7] L1248 [F16]
  rw [show [F7] ++ L1248 ++ [F16] = L8127 from rfl, show [F7] ++ L1248 = L1244 from rfl,
    show L1248 ++ [F16] = L8126 from rfl] at h
  rw [i4791 hinj, i603 hinj, i4790 hinj, i606 hinj] at h
  linarith

theorem row1709 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8128 + (1 : ℝ) * HLm Γ 5 L8130 + (-1 : ℝ) * HLm Γ 5 L8132 + (-1 : ℝ) * HLm Γ 5 L8134 := by
  have h := HLm_submod hΓ [F107] L8135 [F67]
  rw [show [F107] ++ L8135 ++ [F67] = L8133 from rfl, show [F107] ++ L8135 = L8129 from rfl,
    show L8135 ++ [F67] = L8131 from rfl] at h
  rw [i4794 hinj, i4792 hinj, i4793 hinj, i4795 hinj] at h
  linarith

theorem row1710 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4221 + (1 : ℝ) * HLm Γ 5 L7362 + (-1 : ℝ) * HLm Γ 5 L4366 + (-1 : ℝ) * HLm Γ 5 L3160 := by
  have h := HLm_submod hΓ [F1] L8139 [F210]
  rw [show [F1] ++ L8139 ++ [F210] = L8138 from rfl, show [F1] ++ L8139 = L8136 from rfl,
    show L8139 ++ [F210] = L8137 from rfl] at h
  rw [i4798 hinj, i4796 hinj, i4797 hinj, i4799 hinj] at h
  linarith

theorem row1711 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6817 + (1 : ℝ) * HLm Γ 5 L8141 + (-1 : ℝ) * HLm Γ 5 L8143 + (-1 : ℝ) * HLm Γ 5 L7378 := by
  have h := HLm_submod hΓ [F7] L8145 [F108]
  rw [show [F7] ++ L8145 ++ [F108] = L8144 from rfl, show [F7] ++ L8145 = L8140 from rfl,
    show L8145 ++ [F108] = L8142 from rfl] at h
  rw [i4802 hinj, i4800 hinj, i4801 hinj, i4803 hinj] at h
  linarith

theorem row1712 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1260 + (1 : ℝ) * HLm Γ 5 L5418 + (-1 : ℝ) * HLm Γ 5 L1758 + (-1 : ℝ) * HLm Γ 5 L1266 := by
  have h := HLm_submod hΓ [F2] L1267 [F67]
  rw [show [F2] ++ L1267 ++ [F67] = L8147 from rfl, show [F2] ++ L1267 = L1261 from rfl,
    show L1267 ++ [F67] = L8146 from rfl] at h
  rw [i4805 hinj, i615 hinj, i4804 hinj, i618 hinj] at h
  linarith

theorem row1713 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L578 + (1 : ℝ) * HLm Γ 5 L8149 + (-1 : ℝ) * HLm Γ 5 L8151 + (-1 : ℝ) * HLm Γ 5 L235 := by
  have h := HLm_submod hΓ [F7] L8153 [F82]
  rw [show [F7] ++ L8153 ++ [F82] = L8152 from rfl, show [F7] ++ L8153 = L8148 from rfl,
    show L8153 ++ [F82] = L8150 from rfl] at h
  rw [i4808 hinj, i4806 hinj, i4807 hinj, i4809 hinj] at h
  linarith

theorem row1714 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8154 + (1 : ℝ) * HLm Γ 5 L8156 + (-1 : ℝ) * HLm Γ 5 L8158 + (-1 : ℝ) * HLm Γ 5 L7152 := by
  have h := HLm_submod hΓ [F16] L8160 [F23]
  rw [show [F16] ++ L8160 ++ [F23] = L8159 from rfl, show [F16] ++ L8160 = L8155 from rfl,
    show L8160 ++ [F23] = L8157 from rfl] at h
  rw [i4812 hinj, i4810 hinj, i4811 hinj, i4813 hinj] at h
  linarith

theorem row1715 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8161 + (1 : ℝ) * HLm Γ 5 L8163 + (-1 : ℝ) * HLm Γ 5 L8165 + (-1 : ℝ) * HLm Γ 5 L8167 := by
  have h := HLm_submod hΓ [F210] L8168 [F43]
  rw [show [F210] ++ L8168 ++ [F43] = L8166 from rfl, show [F210] ++ L8168 = L8162 from rfl,
    show L8168 ++ [F43] = L8164 from rfl] at h
  rw [i4816 hinj, i4814 hinj, i4815 hinj, i4817 hinj] at h
  linarith

theorem row1716 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7136 + (1 : ℝ) * HLm Γ 5 L8170 + (-1 : ℝ) * HLm Γ 5 L8172 + (-1 : ℝ) * HLm Γ 5 L2939 := by
  have h := HLm_submod hΓ [F7] L2940 [F6]
  rw [show [F7] ++ L2940 ++ [F6] = L8173 from rfl, show [F7] ++ L2940 = L8169 from rfl,
    show L2940 ++ [F6] = L8171 from rfl] at h
  rw [i4820 hinj, i4818 hinj, i4819 hinj, i1675 hinj] at h
  linarith

theorem row1717 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L8175 + (-1 : ℝ) * HLm Γ 5 L4558 + (-1 : ℝ) * HLm Γ 5 L8178 := by
  have h := HLm_submod hΓ [F62] L8178 [F219]
  rw [show [F62] ++ L8178 ++ [F219] = L8177 from rfl, show [F62] ++ L8178 = L8174 from rfl,
    show L8178 ++ [F219] = L8176 from rfl] at h
  rw [i4823 hinj, i4821 hinj, i4822 hinj] at h
  linarith

theorem row1718 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8179 + (1 : ℝ) * HLm Γ 5 L8181 + (-1 : ℝ) * HLm Γ 5 L8183 + (-1 : ℝ) * HLm Γ 5 L97 := by
  have h := HLm_submod hΓ [F210] L97 [F33]
  rw [show [F210] ++ L97 ++ [F33] = L8184 from rfl, show [F210] ++ L97 = L8180 from rfl,
    show L97 ++ [F33] = L8182 from rfl] at h
  rw [i4826 hinj, i4824 hinj, i4825 hinj] at h
  linarith

theorem row1719 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7434 + (1 : ℝ) * HLm Γ 5 L7160 + (-1 : ℝ) * HLm Γ 5 L8186 + (-1 : ℝ) * HLm Γ 5 L7159 := by
  have h := HLm_submod hΓ [F1] L7159 [F210]
  rw [show [F1] ++ L7159 ++ [F210] = L8187 from rfl, show [F1] ++ L7159 = L8185 from rfl,
    show L7159 ++ [F210] = L7160 from rfl] at h
  rw [i4828 hinj, i4827 hinj] at h
  linarith

theorem row1720 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1317 + (1 : ℝ) * HLm Γ 5 L8189 + (-1 : ℝ) * HLm Γ 5 L8190 + (-1 : ℝ) * HLm Γ 5 L2200 := by
  have h := HLm_submod hΓ [F67] L2200 [F210]
  rw [show [F67] ++ L2200 ++ [F210] = L8191 from rfl, show [F67] ++ L2200 = L8188 from rfl,
    show L2200 ++ [F210] = L8189 from rfl] at h
  rw [i4830 hinj, i4829 hinj] at h
  linarith

theorem row1721 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8192 + (1 : ℝ) * HLm Γ 5 L8194 + (-1 : ℝ) * HLm Γ 5 L8196 + (-1 : ℝ) * HLm Γ 5 L3230 := by
  have h := HLm_submod hΓ [F210] L3231 [F36]
  rw [show [F210] ++ L3231 ++ [F36] = L8197 from rfl, show [F210] ++ L3231 = L8193 from rfl,
    show L3231 ++ [F36] = L8195 from rfl] at h
  rw [i4833 hinj, i4831 hinj, i4832 hinj, i1825 hinj] at h
  linarith

theorem row1722 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8198 + (1 : ℝ) * HLm Γ 5 L8200 + (-1 : ℝ) * HLm Γ 5 L8202 + (-1 : ℝ) * HLm Γ 5 L101 := by
  have h := HLm_submod hΓ [F210] L101 [F36]
  rw [show [F210] ++ L101 ++ [F36] = L8203 from rfl, show [F210] ++ L101 = L8199 from rfl,
    show L101 ++ [F36] = L8201 from rfl] at h
  rw [i4836 hinj, i4834 hinj, i4835 hinj] at h
  linarith

theorem row1723 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L845 + (1 : ℝ) * HLm Γ 5 L597 + (-1 : ℝ) * HLm Γ 5 L1420 + (-1 : ℝ) * HLm Γ 5 L595 := by
  have h := HLm_submod hΓ [F7] L595 [F3]
  rw [show [F7] ++ L595 ++ [F3] = L8206 from rfl, show [F7] ++ L595 = L8204 from rfl,
    show L595 ++ [F3] = L8205 from rfl] at h
  rw [i4839 hinj, i4837 hinj, i4838 hinj] at h
  linarith

theorem row1724 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8207 + (1 : ℝ) * HLm Γ 5 L8209 + (-1 : ℝ) * HLm Γ 5 L8211 + (-1 : ℝ) * HLm Γ 5 L7675 := by
  have h := HLm_submod hΓ [F46] L7676 [F217]
  rw [show [F46] ++ L7676 ++ [F217] = L8212 from rfl, show [F46] ++ L7676 = L8208 from rfl,
    show L7676 ++ [F217] = L8210 from rfl] at h
  rw [i4842 hinj, i4840 hinj, i4841 hinj, i4540 hinj] at h
  linarith

theorem row1725 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8213 + (1 : ℝ) * HLm Γ 5 L8215 + (-1 : ℝ) * HLm Γ 5 L8217 + (-1 : ℝ) * HLm Γ 5 L8219 := by
  have h := HLm_submod hΓ [F7] L8220 [F6]
  rw [show [F7] ++ L8220 ++ [F6] = L8218 from rfl, show [F7] ++ L8220 = L8214 from rfl,
    show L8220 ++ [F6] = L8216 from rfl] at h
  rw [i4845 hinj, i4843 hinj, i4844 hinj, i4846 hinj] at h
  linarith

theorem row1726 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8221 + (1 : ℝ) * HLm Γ 5 L8223 + (-1 : ℝ) * HLm Γ 5 L8225 + (-1 : ℝ) * HLm Γ 5 L8227 := by
  have h := HLm_submod hΓ [F7] L8227 [F6]
  rw [show [F7] ++ L8227 ++ [F6] = L8226 from rfl, show [F7] ++ L8227 = L8222 from rfl,
    show L8227 ++ [F6] = L8224 from rfl] at h
  rw [i4849 hinj, i4847 hinj, i4848 hinj] at h
  linarith

theorem row1727 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8228 + (1 : ℝ) * HLm Γ 5 L8230 + (-1 : ℝ) * HLm Γ 5 L8232 + (-1 : ℝ) * HLm Γ 5 L7204 := by
  have h := HLm_submod hΓ [F210] L8234 [F6]
  rw [show [F210] ++ L8234 ++ [F6] = L8233 from rfl, show [F210] ++ L8234 = L8229 from rfl,
    show L8234 ++ [F6] = L8231 from rfl] at h
  rw [i4852 hinj, i4850 hinj, i4851 hinj, i4853 hinj] at h
  linarith

theorem row1728 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2338 + (1 : ℝ) * HLm Γ 5 L8236 + (-1 : ℝ) * HLm Γ 5 L2827 + (-1 : ℝ) * HLm Γ 5 L8239 := by
  have h := HLm_submod hΓ [F7] L8239 [F2]
  rw [show [F7] ++ L8239 ++ [F2] = L8238 from rfl, show [F7] ++ L8239 = L8235 from rfl,
    show L8239 ++ [F2] = L8237 from rfl] at h
  rw [i4856 hinj, i4854 hinj, i4855 hinj] at h
  linarith

theorem row1729 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8240 + (1 : ℝ) * HLm Γ 5 L8242 + (-1 : ℝ) * HLm Γ 5 L8244 + (-1 : ℝ) * HLm Γ 5 L986 := by
  have h := HLm_submod hΓ [F2] L987 [F228]
  rw [show [F2] ++ L987 ++ [F228] = L8245 from rfl, show [F2] ++ L987 = L8241 from rfl,
    show L987 ++ [F228] = L8243 from rfl] at h
  rw [i4859 hinj, i4857 hinj, i4858 hinj, i458 hinj] at h
  linarith

theorem row1730 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8246 + (1 : ℝ) * HLm Γ 5 L4261 + (-1 : ℝ) * HLm Γ 5 L8249 + (-1 : ℝ) * HLm Γ 5 L3247 := by
  have h := HLm_submod hΓ [F44] L4267 [F210]
  rw [show [F44] ++ L4267 ++ [F210] = L8250 from rfl, show [F44] ++ L4267 = L8247 from rfl,
    show L4267 ++ [F210] = L8248 from rfl] at h
  rw [i4862 hinj, i4860 hinj, i4861 hinj, i2388 hinj] at h
  linarith

theorem row1731 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8251 + (1 : ℝ) * HLm Γ 5 L8253 + (-1 : ℝ) * HLm Γ 5 L8255 + (-1 : ℝ) * HLm Γ 5 L8257 := by
  have h := HLm_submod hΓ [F7] L8258 [F218]
  rw [show [F7] ++ L8258 ++ [F218] = L8256 from rfl, show [F7] ++ L8258 = L8252 from rfl,
    show L8258 ++ [F218] = L8254 from rfl] at h
  rw [i4865 hinj, i4863 hinj, i4864 hinj, i4866 hinj] at h
  linarith

theorem row1732 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8259 + (1 : ℝ) * HLm Γ 5 L5549 + (-1 : ℝ) * HLm Γ 5 L4842 + (-1 : ℝ) * HLm Γ 5 L3239 := by
  have h := HLm_submod hΓ [F7] L8261 [F86]
  rw [show [F7] ++ L8261 ++ [F86] = L5546 from rfl, show [F7] ++ L8261 = L8260 from rfl,
    show L8261 ++ [F86] = L5550 from rfl] at h
  rw [i3136 hinj, i4867 hinj, i3139 hinj, i4868 hinj] at h
  linarith

theorem row1733 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8262 + (1 : ℝ) * HLm Γ 5 L8264 + (-1 : ℝ) * HLm Γ 5 L8266 + (-1 : ℝ) * HLm Γ 5 L8268 := by
  have h := HLm_submod hΓ [F210] L8269 [F43]
  rw [show [F210] ++ L8269 ++ [F43] = L8267 from rfl, show [F210] ++ L8269 = L8263 from rfl,
    show L8269 ++ [F43] = L8265 from rfl] at h
  rw [i4871 hinj, i4869 hinj, i4870 hinj, i4872 hinj] at h
  linarith

theorem row1734 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4452 + (1 : ℝ) * HLm Γ 5 L8271 + (-1 : ℝ) * HLm Γ 5 L4455 + (-1 : ℝ) * HLm Γ 5 L8274 := by
  have h := HLm_submod hΓ [F7] L8275 [F236]
  rw [show [F7] ++ L8275 ++ [F236] = L8273 from rfl, show [F7] ++ L8275 = L8270 from rfl,
    show L8275 ++ [F236] = L8272 from rfl] at h
  rw [i4875 hinj, i4873 hinj, i4874 hinj, i4876 hinj] at h
  linarith

theorem row1735 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7278 + (1 : ℝ) * HLm Γ 5 L8277 + (-1 : ℝ) * HLm Γ 5 L8279 + (-1 : ℝ) * HLm Γ 5 L8281 := by
  have h := HLm_submod hΓ [F7] L8282 [F210]
  rw [show [F7] ++ L8282 ++ [F210] = L8280 from rfl, show [F7] ++ L8282 = L8276 from rfl,
    show L8282 ++ [F210] = L8278 from rfl] at h
  rw [i4879 hinj, i4877 hinj, i4878 hinj, i4880 hinj] at h
  linarith

theorem row1736 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8283 + (1 : ℝ) * HLm Γ 5 L8285 + (-1 : ℝ) * HLm Γ 5 L4503 + (-1 : ℝ) * HLm Γ 5 L8288 := by
  have h := HLm_submod hΓ [F7] L8289 [F218]
  rw [show [F7] ++ L8289 ++ [F218] = L8287 from rfl, show [F7] ++ L8289 = L8284 from rfl,
    show L8289 ++ [F218] = L8286 from rfl] at h
  rw [i4883 hinj, i4881 hinj, i4882 hinj, i4884 hinj] at h
  linarith

theorem row1737 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8290 + (1 : ℝ) * HLm Γ 5 L8292 + (-1 : ℝ) * HLm Γ 5 L8294 + (-1 : ℝ) * HLm Γ 5 L8296 := by
  have h := HLm_submod hΓ [F7] L8296 [F33]
  rw [show [F7] ++ L8296 ++ [F33] = L8295 from rfl, show [F7] ++ L8296 = L8291 from rfl,
    show L8296 ++ [F33] = L8293 from rfl] at h
  rw [i4887 hinj, i4885 hinj, i4886 hinj] at h
  linarith

theorem row1738 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7533 + (1 : ℝ) * HLm Γ 5 L8298 + (-1 : ℝ) * HLm Γ 5 L8300 + (-1 : ℝ) * HLm Γ 5 L8302 := by
  have h := HLm_submod hΓ [F7] L8302 [F33]
  rw [show [F7] ++ L8302 ++ [F33] = L8301 from rfl, show [F7] ++ L8302 = L8297 from rfl,
    show L8302 ++ [F33] = L8299 from rfl] at h
  rw [i4890 hinj, i4888 hinj, i4889 hinj] at h
  linarith

theorem row1739 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7155 + (1 : ℝ) * HLm Γ 5 L8304 + (-1 : ℝ) * HLm Γ 5 L8306 + (-1 : ℝ) * HLm Γ 5 L7181 := by
  have h := HLm_submod hΓ [F3] L7181 [F16]
  rw [show [F3] ++ L7181 ++ [F16] = L8307 from rfl, show [F3] ++ L7181 = L8303 from rfl,
    show L7181 ++ [F16] = L8305 from rfl] at h
  rw [i4893 hinj, i4891 hinj, i4892 hinj] at h
  linarith

theorem row1740 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8308 + (1 : ℝ) * HLm Γ 5 L7188 + (-1 : ℝ) * HLm Γ 5 L8311 + (-1 : ℝ) * HLm Γ 5 L7186 := by
  have h := HLm_submod hΓ [F44] L7187 [F210]
  rw [show [F44] ++ L7187 ++ [F210] = L8312 from rfl, show [F44] ++ L7187 = L8309 from rfl,
    show L7187 ++ [F210] = L8310 from rfl] at h
  rw [i4896 hinj, i4894 hinj, i4895 hinj, i4263 hinj] at h
  linarith

theorem row1741 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8313 + (1 : ℝ) * HLm Γ 5 L8315 + (-1 : ℝ) * HLm Γ 5 L8317 + (-1 : ℝ) * HLm Γ 5 L8319 := by
  have h := HLm_submod hΓ [F7] L8320 [F43]
  rw [show [F7] ++ L8320 ++ [F43] = L8318 from rfl, show [F7] ++ L8320 = L8314 from rfl,
    show L8320 ++ [F43] = L8316 from rfl] at h
  rw [i4899 hinj, i4897 hinj, i4898 hinj, i4900 hinj] at h
  linarith

theorem row1742 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3447 + (1 : ℝ) * HLm Γ 5 L8322 + (-1 : ℝ) * HLm Γ 5 L8324 + (-1 : ℝ) * HLm Γ 5 L7192 := by
  have h := HLm_submod hΓ [F1] L7193 [F228]
  rw [show [F1] ++ L7193 ++ [F228] = L8325 from rfl, show [F1] ++ L7193 = L8321 from rfl,
    show L7193 ++ [F228] = L8323 from rfl] at h
  rw [i4903 hinj, i4901 hinj, i4902 hinj, i4266 hinj] at h
  linarith

theorem row1743 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8326 + (1 : ℝ) * HLm Γ 5 L7212 + (-1 : ℝ) * HLm Γ 5 L8329 + (-1 : ℝ) * HLm Γ 5 L7210 := by
  have h := HLm_submod hΓ [F16] L7211 [F228]
  rw [show [F16] ++ L7211 ++ [F228] = L8330 from rfl, show [F16] ++ L7211 = L8327 from rfl,
    show L7211 ++ [F228] = L8328 from rfl] at h
  rw [i4906 hinj, i4904 hinj, i4905 hinj, i4276 hinj] at h
  linarith

theorem row1744 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4891 + (1 : ℝ) * HLm Γ 5 L8332 + (-1 : ℝ) * HLm Γ 5 L4895 + (-1 : ℝ) * HLm Γ 5 L774 := by
  have h := HLm_submod hΓ [F228] L8335 [F6]
  rw [show [F228] ++ L8335 ++ [F6] = L8334 from rfl, show [F228] ++ L8335 = L8331 from rfl,
    show L8335 ++ [F6] = L8333 from rfl] at h
  rw [i4909 hinj, i4907 hinj, i4908 hinj, i4910 hinj] at h
  linarith

theorem row1745 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8336 + (1 : ℝ) * HLm Γ 5 L8338 + (-1 : ℝ) * HLm Γ 5 L8340 + (-1 : ℝ) * HLm Γ 5 L8342 := by
  have h := HLm_submod hΓ [F67] L8343 [F30]
  rw [show [F67] ++ L8343 ++ [F30] = L8341 from rfl, show [F67] ++ L8343 = L8337 from rfl,
    show L8343 ++ [F30] = L8339 from rfl] at h
  rw [i4913 hinj, i4911 hinj, i4912 hinj, i4914 hinj] at h
  linarith

theorem row1746 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7117 + (1 : ℝ) * HLm Γ 5 L8345 + (-1 : ℝ) * HLm Γ 5 L8347 + (-1 : ℝ) * HLm Γ 5 L3287 := by
  have h := HLm_submod hΓ [F2] L3288 [F228]
  rw [show [F2] ++ L3288 ++ [F228] = L8348 from rfl, show [F2] ++ L3288 = L8344 from rfl,
    show L3288 ++ [F228] = L8346 from rfl] at h
  rw [i4917 hinj, i4915 hinj, i4916 hinj, i1853 hinj] at h
  linarith

theorem row1747 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7216 + (1 : ℝ) * HLm Γ 5 L4097 + (-1 : ℝ) * HLm Γ 5 L6034 + (-1 : ℝ) * HLm Γ 5 L2950 := by
  have h := HLm_submod hΓ [F0] L2951 [F16]
  rw [show [F0] ++ L2951 ++ [F16] = L8350 from rfl, show [F0] ++ L2951 = L7217 from rfl,
    show L2951 ++ [F16] = L8349 from rfl] at h
  rw [i4919 hinj, i4280 hinj, i4918 hinj, i1681 hinj] at h
  linarith

theorem row1748 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8351 + (1 : ℝ) * HLm Γ 5 L7221 + (-1 : ℝ) * HLm Γ 5 L8354 + (-1 : ℝ) * HLm Γ 5 L7218 := by
  have h := HLm_submod hΓ [F44] L8356 [F218]
  rw [show [F44] ++ L8356 ++ [F218] = L8355 from rfl, show [F44] ++ L8356 = L8352 from rfl,
    show L8356 ++ [F218] = L8353 from rfl] at h
  rw [i4922 hinj, i4920 hinj, i4921 hinj, i4923 hinj] at h
  linarith

theorem row1749 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8357 + (1 : ℝ) * HLm Γ 5 L8359 + (-1 : ℝ) * HLm Γ 5 L8361 + (-1 : ℝ) * HLm Γ 5 L1135 := by
  have h := HLm_submod hΓ [F210] L8363 [F85]
  rw [show [F210] ++ L8363 ++ [F85] = L8362 from rfl, show [F210] ++ L8363 = L8358 from rfl,
    show L8363 ++ [F85] = L8360 from rfl] at h
  rw [i4926 hinj, i4924 hinj, i4925 hinj, i4927 hinj] at h
  linarith

theorem row1750 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8364 + (1 : ℝ) * HLm Γ 5 L7239 + (-1 : ℝ) * HLm Γ 5 L8367 + (-1 : ℝ) * HLm Γ 5 L8369 := by
  have h := HLm_submod hΓ [F2] L8370 [F27]
  rw [show [F2] ++ L8370 ++ [F27] = L8368 from rfl, show [F2] ++ L8370 = L8365 from rfl,
    show L8370 ++ [F27] = L8366 from rfl] at h
  rw [i4930 hinj, i4928 hinj, i4929 hinj, i4931 hinj] at h
  linarith

theorem row1751 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2433 + (1 : ℝ) * HLm Γ 5 L4334 + (-1 : ℝ) * HLm Γ 5 L8372 + (-1 : ℝ) * HLm Γ 5 L3292 := by
  have h := HLm_submod hΓ [F22] L4338 [F210]
  rw [show [F22] ++ L4338 ++ [F210] = L8373 from rfl, show [F22] ++ L4338 = L8371 from rfl,
    show L4338 ++ [F210] = L4335 from rfl] at h
  rw [i4933 hinj, i4932 hinj, i2431 hinj, i2433 hinj] at h
  linarith

theorem row1752 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8374 + (1 : ℝ) * HLm Γ 5 L4341 + (-1 : ℝ) * HLm Γ 5 L8376 + (-1 : ℝ) * HLm Γ 5 L4345 := by
  have h := HLm_submod hΓ [F111] L4346 [F210]
  rw [show [F111] ++ L4346 ++ [F210] = L8377 from rfl, show [F111] ++ L4346 = L8375 from rfl,
    show L4346 ++ [F210] = L4342 from rfl] at h
  rw [i4935 hinj, i4934 hinj, i2435 hinj, i2437 hinj] at h
  linarith

theorem row1753 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8378 + (1 : ℝ) * HLm Γ 5 L7917 + (-1 : ℝ) * HLm Γ 5 L4596 + (-1 : ℝ) * HLm Γ 5 L7914 := by
  have h := HLm_submod hΓ [F2] L7915 [F27]
  rw [show [F2] ++ L7915 ++ [F27] = L8380 from rfl, show [F2] ++ L7915 = L8379 from rfl,
    show L7915 ++ [F27] = L7918 from rfl] at h
  rw [i4937 hinj, i4936 hinj, i4670 hinj, i4668 hinj] at h
  linarith

theorem row1754 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7247 + (1 : ℝ) * HLm Γ 5 L8382 + (-1 : ℝ) * HLm Γ 5 L8384 + (-1 : ℝ) * HLm Γ 5 L7245 := by
  have h := HLm_submod hΓ [F7] L8386 [F16]
  rw [show [F7] ++ L8386 ++ [F16] = L8385 from rfl, show [F7] ++ L8386 = L8381 from rfl,
    show L8386 ++ [F16] = L8383 from rfl] at h
  rw [i4940 hinj, i4938 hinj, i4939 hinj, i4941 hinj] at h
  linarith

theorem row1755 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4138 + (1 : ℝ) * HLm Γ 5 L7953 + (-1 : ℝ) * HLm Γ 5 L8389 + (-1 : ℝ) * HLm Γ 5 L1123 := by
  have h := HLm_submod hΓ [F2] L1124 [F228]
  rw [show [F2] ++ L1124 ++ [F228] = L8390 from rfl, show [F2] ++ L1124 = L8387 from rfl,
    show L1124 ++ [F228] = L8388 from rfl] at h
  rw [i4944 hinj, i4942 hinj, i4943 hinj, i534 hinj] at h
  linarith

theorem row1756 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2720 + (1 : ℝ) * HLm Γ 5 L8053 + (-1 : ℝ) * HLm Γ 5 L8393 + (-1 : ℝ) * HLm Γ 5 L1123 := by
  have h := HLm_submod hΓ [F12] L1124 [F210]
  rw [show [F12] ++ L1124 ++ [F210] = L8394 from rfl, show [F12] ++ L1124 = L8391 from rfl,
    show L1124 ++ [F210] = L8392 from rfl] at h
  rw [i4947 hinj, i4945 hinj, i4946 hinj, i534 hinj] at h
  linarith

theorem row1757 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1376 + (1 : ℝ) * HLm Γ 5 L8396 + (-1 : ℝ) * HLm Γ 5 L8398 + (-1 : ℝ) * HLm Γ 5 L707 := by
  have h := HLm_submod hΓ [F16] L1355 [F52]
  rw [show [F16] ++ L1355 ++ [F52] = L8399 from rfl, show [F16] ++ L1355 = L8395 from rfl,
    show L1355 ++ [F52] = L8397 from rfl] at h
  rw [i4950 hinj, i4948 hinj, i4949 hinj, i672 hinj] at h
  linarith

theorem row1758 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8400 + (1 : ℝ) * HLm Γ 5 L8402 + (-1 : ℝ) * HLm Γ 5 L8404 + (-1 : ℝ) * HLm Γ 5 L897 := by
  have h := HLm_submod hΓ [F67] L1359 [F33]
  rw [show [F67] ++ L1359 ++ [F33] = L8405 from rfl, show [F67] ++ L1359 = L8401 from rfl,
    show L1359 ++ [F33] = L8403 from rfl] at h
  rw [i4953 hinj, i4951 hinj, i4952 hinj, i676 hinj] at h
  linarith

theorem row1759 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4206 + (1 : ℝ) * HLm Γ 5 L7833 + (-1 : ℝ) * HLm Γ 5 L4210 + (-1 : ℝ) * HLm Γ 5 L4374 := by
  have h := HLm_submod hΓ [F0] L4375 [F36]
  rw [show [F0] ++ L4375 ++ [F36] = L8408 from rfl, show [F0] ++ L4375 = L8406 from rfl,
    show L4375 ++ [F36] = L8407 from rfl] at h
  rw [i4956 hinj, i4954 hinj, i4955 hinj, i2452 hinj] at h
  linarith

theorem row1760 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7251 + (1 : ℝ) * HLm Γ 5 L7618 + (-1 : ℝ) * HLm Γ 5 L8410 + (-1 : ℝ) * HLm Γ 5 L7334 := by
  have h := HLm_submod hΓ [F51] L7334 [F16]
  rw [show [F51] ++ L7334 ++ [F16] = L8411 from rfl, show [F51] ++ L7334 = L7251 from rfl,
    show L7334 ++ [F16] = L8409 from rfl] at h
  rw [i4958 hinj, i4957 hinj] at h
  linarith

theorem row1761 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8412 + (1 : ℝ) * HLm Γ 5 L7402 + (-1 : ℝ) * HLm Γ 5 L8414 + (-1 : ℝ) * HLm Γ 5 L7399 := by
  have h := HLm_submod hΓ [F0] L7400 [F6]
  rw [show [F0] ++ L7400 ++ [F6] = L8415 from rfl, show [F0] ++ L7400 = L8413 from rfl,
    show L7400 ++ [F6] = L7403 from rfl] at h
  rw [i4960 hinj, i4959 hinj, i4385 hinj, i4383 hinj] at h
  linarith

theorem row1762 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8416 + (1 : ℝ) * HLm Γ 5 L8418 + (-1 : ℝ) * HLm Γ 5 L8420 + (-1 : ℝ) * HLm Γ 5 L2230 := by
  have h := HLm_submod hΓ [F21] L2231 [F210]
  rw [show [F21] ++ L2231 ++ [F210] = L8421 from rfl, show [F21] ++ L2231 = L8417 from rfl,
    show L2231 ++ [F210] = L8419 from rfl] at h
  rw [i4963 hinj, i4961 hinj, i4962 hinj, i1226 hinj] at h
  linarith

theorem row1763 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8422 + (1 : ℝ) * HLm Γ 5 L5715 + (-1 : ℝ) * HLm Γ 5 L8425 + (-1 : ℝ) * HLm Γ 5 L3379 := by
  have h := HLm_submod hΓ [F214] L4402 [F45]
  rw [show [F214] ++ L4402 ++ [F45] = L8426 from rfl, show [F214] ++ L4402 = L8423 from rfl,
    show L4402 ++ [F45] = L8424 from rfl] at h
  rw [i4966 hinj, i4964 hinj, i4965 hinj, i2468 hinj] at h
  linarith

theorem row1764 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8427 + (1 : ℝ) * HLm Γ 5 L4174 + (-1 : ℝ) * HLm Γ 5 L8430 + (-1 : ℝ) * HLm Γ 5 L866 := by
  have h := HLm_submod hΓ [F86] L867 [F218]
  rw [show [F86] ++ L867 ++ [F218] = L8431 from rfl, show [F86] ++ L867 = L8428 from rfl,
    show L867 ++ [F218] = L8429 from rfl] at h
  rw [i4969 hinj, i4967 hinj, i4968 hinj, i394 hinj] at h
  linarith

theorem row1765 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8432 + (1 : ℝ) * HLm Γ 5 L8434 + (-1 : ℝ) * HLm Γ 5 L8436 + (-1 : ℝ) * HLm Γ 5 L7325 := by
  have h := HLm_submod hΓ [F210] L8438 [F43]
  rw [show [F210] ++ L8438 ++ [F43] = L8437 from rfl, show [F210] ++ L8438 = L8433 from rfl,
    show L8438 ++ [F43] = L8435 from rfl] at h
  rw [i4972 hinj, i4970 hinj, i4971 hinj, i4973 hinj] at h
  linarith

theorem row1766 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2601 + (1 : ℝ) * HLm Γ 5 L2438 + (-1 : ℝ) * HLm Γ 5 L1785 + (-1 : ℝ) * HLm Γ 5 L7331 := by
  have h := HLm_submod hΓ [F1] L8442 [F16]
  rw [show [F1] ++ L8442 ++ [F16] = L8441 from rfl, show [F1] ++ L8442 = L8439 from rfl,
    show L8442 ++ [F16] = L8440 from rfl] at h
  rw [i4976 hinj, i4974 hinj, i4975 hinj, i4977 hinj] at h
  linarith

theorem row1767 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L767 + (1 : ℝ) * HLm Γ 5 L8444 + (-1 : ℝ) * HLm Γ 5 L8446 + (-1 : ℝ) * HLm Γ 5 L8448 := by
  have h := HLm_submod hΓ [F0] L8449 [F218]
  rw [show [F0] ++ L8449 ++ [F218] = L8447 from rfl, show [F0] ++ L8449 = L8443 from rfl,
    show L8449 ++ [F218] = L8445 from rfl] at h
  rw [i4980 hinj, i4978 hinj, i4979 hinj, i4981 hinj] at h
  linarith

theorem row1768 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7321 + (1 : ℝ) * HLm Γ 5 L8451 + (-1 : ℝ) * HLm Γ 5 L2683 + (-1 : ℝ) * HLm Γ 5 L654 := by
  have h := HLm_submod hΓ [F0] L8454 [F43]
  rw [show [F0] ++ L8454 ++ [F43] = L8453 from rfl, show [F0] ++ L8454 = L8450 from rfl,
    show L8454 ++ [F43] = L8452 from rfl] at h
  rw [i4984 hinj, i4982 hinj, i4983 hinj, i4985 hinj] at h
  linarith

theorem row1769 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8455 + (1 : ℝ) * HLm Γ 5 L8457 + (-1 : ℝ) * HLm Γ 5 L8459 + (-1 : ℝ) * HLm Γ 5 L654 := by
  have h := HLm_submod hΓ [F51] L8454 [F218]
  rw [show [F51] ++ L8454 ++ [F218] = L8460 from rfl, show [F51] ++ L8454 = L8456 from rfl,
    show L8454 ++ [F218] = L8458 from rfl] at h
  rw [i4988 hinj, i4986 hinj, i4987 hinj, i4985 hinj] at h
  linarith

theorem row1770 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L658 + (1 : ℝ) * HLm Γ 5 L8462 + (-1 : ℝ) * HLm Γ 5 L8464 + (-1 : ℝ) * HLm Γ 5 L654 := by
  have h := HLm_submod hΓ [F52] L8454 [F214]
  rw [show [F52] ++ L8454 ++ [F214] = L8465 from rfl, show [F52] ++ L8454 = L8461 from rfl,
    show L8454 ++ [F214] = L8463 from rfl] at h
  rw [i4991 hinj, i4989 hinj, i4990 hinj, i4985 hinj] at h
  linarith

theorem row1771 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8466 + (1 : ℝ) * HLm Γ 5 L8468 + (-1 : ℝ) * HLm Γ 5 L8470 + (-1 : ℝ) * HLm Γ 5 L8472 := by
  have h := HLm_submod hΓ [F0] L8473 [F36]
  rw [show [F0] ++ L8473 ++ [F36] = L8471 from rfl, show [F0] ++ L8473 = L8467 from rfl,
    show L8473 ++ [F36] = L8469 from rfl] at h
  rw [i4994 hinj, i4992 hinj, i4993 hinj, i4995 hinj] at h
  linarith

theorem row1772 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7936 + (1 : ℝ) * HLm Γ 5 L8475 + (-1 : ℝ) * HLm Γ 5 L8477 + (-1 : ℝ) * HLm Γ 5 L7597 := by
  have h := HLm_submod hΓ [F211] L7598 [F36]
  rw [show [F211] ++ L7598 ++ [F36] = L8478 from rfl, show [F211] ++ L7598 = L8474 from rfl,
    show L7598 ++ [F36] = L8476 from rfl] at h
  rw [i4998 hinj, i4996 hinj, i4997 hinj, i4495 hinj] at h
  linarith

theorem row1773 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8479 + (1 : ℝ) * HLm Γ 5 L3401 + (-1 : ℝ) * HLm Γ 5 L8482 + (-1 : ℝ) * HLm Γ 5 L2579 := by
  have h := HLm_submod hΓ [F108] L2580 [F211]
  rw [show [F108] ++ L2580 ++ [F211] = L8483 from rfl, show [F108] ++ L2580 = L8480 from rfl,
    show L2580 ++ [F211] = L8481 from rfl] at h
  rw [i5001 hinj, i4999 hinj, i5000 hinj, i1439 hinj] at h
  linarith

theorem row1774 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7136 + (1 : ℝ) * HLm Γ 5 L8117 + (-1 : ℝ) * HLm Γ 5 L8172 + (-1 : ℝ) * HLm Γ 5 L7345 := by
  have h := HLm_submod hΓ [F0] L8487 [F6]
  rw [show [F0] ++ L8487 ++ [F6] = L8486 from rfl, show [F0] ++ L8487 = L8484 from rfl,
    show L8487 ++ [F6] = L8485 from rfl] at h
  rw [i5004 hinj, i5002 hinj, i5003 hinj, i5005 hinj] at h
  linarith

theorem row1775 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6893 + (1 : ℝ) * HLm Γ 5 L7566 + (-1 : ℝ) * HLm Γ 5 L3517 + (-1 : ℝ) * HLm Γ 5 L7606 := by
  have h := HLm_submod hΓ [F1] L7607 [F0]
  rw [show [F1] ++ L7607 ++ [F0] = L8490 from rfl, show [F1] ++ L7607 = L8488 from rfl,
    show L7607 ++ [F0] = L8489 from rfl] at h
  rw [i5008 hinj, i5006 hinj, i5007 hinj, i4500 hinj] at h
  linarith

theorem row1776 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4423 + (1 : ℝ) * HLm Γ 5 L5105 + (-1 : ℝ) * HLm Γ 5 L8493 + (-1 : ℝ) * HLm Γ 5 L8495 := by
  have h := HLm_submod hΓ [F3] L8496 [F67]
  rw [show [F3] ++ L8496 ++ [F67] = L8494 from rfl, show [F3] ++ L8496 = L8491 from rfl,
    show L8496 ++ [F67] = L8492 from rfl] at h
  rw [i5011 hinj, i5009 hinj, i5010 hinj, i5012 hinj] at h
  linarith

theorem row1777 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4777 + (1 : ℝ) * HLm Γ 5 L8498 + (-1 : ℝ) * HLm Γ 5 L8500 + (-1 : ℝ) * HLm Γ 5 L8502 := by
  have h := HLm_submod hΓ [F0] L8503 [F2]
  rw [show [F0] ++ L8503 ++ [F2] = L8501 from rfl, show [F0] ++ L8503 = L8497 from rfl,
    show L8503 ++ [F2] = L8499 from rfl] at h
  rw [i5015 hinj, i5013 hinj, i5014 hinj, i5016 hinj] at h
  linarith

theorem row1778 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8504 + (1 : ℝ) * HLm Γ 5 L8506 + (-1 : ℝ) * HLm Γ 5 L8508 + (-1 : ℝ) * HLm Γ 5 L8510 := by
  have h := HLm_submod hΓ [F3] L8511 [F211]
  rw [show [F3] ++ L8511 ++ [F211] = L8509 from rfl, show [F3] ++ L8511 = L8505 from rfl,
    show L8511 ++ [F211] = L8507 from rfl] at h
  rw [i5019 hinj, i5017 hinj, i5018 hinj, i5020 hinj] at h
  linarith

theorem row1779 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1630 + (1 : ℝ) * HLm Γ 5 L8513 + (-1 : ℝ) * HLm Γ 5 L8515 + (-1 : ℝ) * HLm Γ 5 L4437 := by
  have h := HLm_submod hΓ [F0] L4438 [F219]
  rw [show [F0] ++ L4438 ++ [F219] = L8516 from rfl, show [F0] ++ L4438 = L8512 from rfl,
    show L4438 ++ [F219] = L8514 from rfl] at h
  rw [i5023 hinj, i5021 hinj, i5022 hinj, i2488 hinj] at h
  linarith

theorem row1780 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1438 + (1 : ℝ) * HLm Γ 5 L8517 + (-1 : ℝ) * HLm Γ 5 L5632 + (-1 : ℝ) * HLm Γ 5 L1157 := by
  have h := HLm_submod hΓ [F2] L1444 [F219]
  rw [show [F2] ++ L1444 ++ [F219] = L8519 from rfl, show [F2] ++ L1444 = L1439 from rfl,
    show L1444 ++ [F219] = L8518 from rfl] at h
  rw [i5025 hinj, i724 hinj, i5024 hinj, i727 hinj] at h
  linarith

theorem row1781 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7514 + (1 : ℝ) * HLm Γ 5 L8521 + (-1 : ℝ) * HLm Γ 5 L8523 + (-1 : ℝ) * HLm Γ 5 L8525 := by
  have h := HLm_submod hΓ [F0] L8526 [F2]
  rw [show [F0] ++ L8526 ++ [F2] = L8524 from rfl, show [F0] ++ L8526 = L8520 from rfl,
    show L8526 ++ [F2] = L8522 from rfl] at h
  rw [i5028 hinj, i5026 hinj, i5027 hinj, i5029 hinj] at h
  linarith

theorem row1782 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4832 + (1 : ℝ) * HLm Γ 5 L7312 + (-1 : ℝ) * HLm Γ 5 L4274 + (-1 : ℝ) * HLm Γ 5 L8530 := by
  have h := HLm_submod hΓ [F0] L8531 [F34]
  rw [show [F0] ++ L8531 ++ [F34] = L8529 from rfl, show [F0] ++ L8531 = L8527 from rfl,
    show L8531 ++ [F34] = L8528 from rfl] at h
  rw [i5032 hinj, i5030 hinj, i5031 hinj, i5033 hinj] at h
  linarith

theorem row1783 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L338 + (1 : ℝ) * HLm Γ 5 L7296 + (-1 : ℝ) * HLm Γ 5 L4842 + (-1 : ℝ) * HLm Γ 5 L6999 := by
  have h := HLm_submod hΓ [F0] L8535 [F210]
  rw [show [F0] ++ L8535 ++ [F210] = L8534 from rfl, show [F0] ++ L8535 = L8532 from rfl,
    show L8535 ++ [F210] = L8533 from rfl] at h
  rw [i5036 hinj, i5034 hinj, i5035 hinj, i5037 hinj] at h
  linarith

theorem row1784 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1458 + (1 : ℝ) * HLm Γ 5 L8537 + (-1 : ℝ) * HLm Γ 5 L8539 + (-1 : ℝ) * HLm Γ 5 L7308 := by
  have h := HLm_submod hΓ [F0] L8541 [F218]
  rw [show [F0] ++ L8541 ++ [F218] = L8540 from rfl, show [F0] ++ L8541 = L8536 from rfl,
    show L8541 ++ [F218] = L8538 from rfl] at h
  rw [i5040 hinj, i5038 hinj, i5039 hinj, i5041 hinj] at h
  linarith

theorem row1785 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8542 + (1 : ℝ) * HLm Γ 5 L8544 + (-1 : ℝ) * HLm Γ 5 L8546 + (-1 : ℝ) * HLm Γ 5 L7316 := by
  have h := HLm_submod hΓ [F2] L8548 [F210]
  rw [show [F2] ++ L8548 ++ [F210] = L8547 from rfl, show [F2] ++ L8548 = L8543 from rfl,
    show L8548 ++ [F210] = L8545 from rfl] at h
  rw [i5044 hinj, i5042 hinj, i5043 hinj, i5045 hinj] at h
  linarith

theorem row1786 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L338 + (1 : ℝ) * HLm Γ 5 L8550 + (-1 : ℝ) * HLm Γ 5 L8552 + (-1 : ℝ) * HLm Γ 5 L7327 := by
  have h := HLm_submod hΓ [F0] L8554 [F219]
  rw [show [F0] ++ L8554 ++ [F219] = L8553 from rfl, show [F0] ++ L8554 = L8549 from rfl,
    show L8554 ++ [F219] = L8551 from rfl] at h
  rw [i5048 hinj, i5046 hinj, i5047 hinj, i5049 hinj] at h
  linarith

theorem row1787 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4832 + (1 : ℝ) * HLm Γ 5 L8556 + (-1 : ℝ) * HLm Γ 5 L4835 + (-1 : ℝ) * HLm Γ 5 L8559 := by
  have h := HLm_submod hΓ [F0] L8560 [F55]
  rw [show [F0] ++ L8560 ++ [F55] = L8558 from rfl, show [F0] ++ L8560 = L8555 from rfl,
    show L8560 ++ [F55] = L8557 from rfl] at h
  rw [i5052 hinj, i5050 hinj, i5051 hinj, i5053 hinj] at h
  linarith

theorem row1788 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1458 + (1 : ℝ) * HLm Γ 5 L7820 + (-1 : ℝ) * HLm Γ 5 L4274 + (-1 : ℝ) * HLm Γ 5 L7818 := by
  have h := HLm_submod hΓ [F0] L8564 [F214]
  rw [show [F0] ++ L8564 ++ [F214] = L8563 from rfl, show [F0] ++ L8564 = L8561 from rfl,
    show L8564 ++ [F214] = L8562 from rfl] at h
  rw [i5056 hinj, i5054 hinj, i5055 hinj, i5057 hinj] at h
  linarith

theorem row1789 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7278 + (1 : ℝ) * HLm Γ 5 L8565 + (-1 : ℝ) * HLm Γ 5 L8567 + (-1 : ℝ) * HLm Γ 5 L2869 := by
  have h := HLm_submod hΓ [F0] L7277 [F3]
  rw [show [F0] ++ L7277 ++ [F3] = L8568 from rfl, show [F0] ++ L7277 = L7279 from rfl,
    show L7277 ++ [F3] = L8566 from rfl] at h
  rw [i5059 hinj, i4316 hinj, i5058 hinj, i4315 hinj] at h
  linarith

theorem row1790 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7833 + (1 : ℝ) * HLm Γ 5 L8570 + (-1 : ℝ) * HLm Γ 5 L8572 + (-1 : ℝ) * HLm Γ 5 L2869 := by
  have h := HLm_submod hΓ [F2] L7277 [F47]
  rw [show [F2] ++ L7277 ++ [F47] = L8573 from rfl, show [F2] ++ L7277 = L8569 from rfl,
    show L7277 ++ [F47] = L8571 from rfl] at h
  rw [i5062 hinj, i5060 hinj, i5061 hinj, i4315 hinj] at h
  linarith

theorem row1791 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8574 + (1 : ℝ) * HLm Γ 5 L8576 + (-1 : ℝ) * HLm Γ 5 L8578 + (-1 : ℝ) * HLm Γ 5 L8580 := by
  have h := HLm_submod hΓ [F210] L8581 [F33]
  rw [show [F210] ++ L8581 ++ [F33] = L8579 from rfl, show [F210] ++ L8581 = L8575 from rfl,
    show L8581 ++ [F33] = L8577 from rfl] at h
  rw [i5065 hinj, i5063 hinj, i5064 hinj, i5066 hinj] at h
  linarith

theorem row1792 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8582 + (1 : ℝ) * HLm Γ 5 L8584 + (-1 : ℝ) * HLm Γ 5 L8586 + (-1 : ℝ) * HLm Γ 5 L8588 := by
  have h := HLm_submod hΓ [F0] L8589 [F55]
  rw [show [F0] ++ L8589 ++ [F55] = L8587 from rfl, show [F0] ++ L8589 = L8583 from rfl,
    show L8589 ++ [F55] = L8585 from rfl] at h
  rw [i5069 hinj, i5067 hinj, i5068 hinj, i5070 hinj] at h
  linarith

theorem row1793 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8283 + (1 : ℝ) * HLm Γ 5 L8591 + (-1 : ℝ) * HLm Γ 5 L8593 + (-1 : ℝ) * HLm Γ 5 L3362 := by
  have h := HLm_submod hΓ [F0] L3363 [F214]
  rw [show [F0] ++ L3363 ++ [F214] = L8594 from rfl, show [F0] ++ L3363 = L8590 from rfl,
    show L3363 ++ [F214] = L8592 from rfl] at h
  rw [i5073 hinj, i5071 hinj, i5072 hinj, i1890 hinj] at h
  linarith

theorem row1794 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8542 + (1 : ℝ) * HLm Γ 5 L8596 + (-1 : ℝ) * HLm Γ 5 L8598 + (-1 : ℝ) * HLm Γ 5 L7283 := by
  have h := HLm_submod hΓ [F2] L7284 [F211]
  rw [show [F2] ++ L7284 ++ [F211] = L8599 from rfl, show [F2] ++ L7284 = L8595 from rfl,
    show L7284 ++ [F211] = L8597 from rfl] at h
  rw [i5076 hinj, i5074 hinj, i5075 hinj, i4319 hinj] at h
  linarith

theorem row1795 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3616 + (1 : ℝ) * HLm Γ 5 L3359 + (-1 : ℝ) * HLm Γ 5 L3618 + (-1 : ℝ) * HLm Γ 5 L7933 := by
  have h := HLm_submod hΓ [F0] L7934 [F5]
  rw [show [F0] ++ L7934 ++ [F5] = L8602 from rfl, show [F0] ++ L7934 = L8600 from rfl,
    show L7934 ++ [F5] = L8601 from rfl] at h
  rw [i5079 hinj, i5077 hinj, i5078 hinj, i4679 hinj] at h
  linarith

theorem row1796 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4452 + (1 : ℝ) * HLm Γ 5 L8604 + (-1 : ℝ) * HLm Γ 5 L4455 + (-1 : ℝ) * HLm Γ 5 L1143 := by
  have h := HLm_submod hΓ [F0] L4535 [F236]
  rw [show [F0] ++ L4535 ++ [F236] = L8606 from rfl, show [F0] ++ L4535 = L8603 from rfl,
    show L4535 ++ [F236] = L8605 from rfl] at h
  rw [i5082 hinj, i5080 hinj, i5081 hinj, i2542 hinj] at h
  linarith

theorem row1797 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1161 + (1 : ℝ) * HLm Γ 5 L8608 + (-1 : ℝ) * HLm Γ 5 L8610 + (-1 : ℝ) * HLm Γ 5 L1143 := by
  have h := HLm_submod hΓ [F108] L4535 [F211]
  rw [show [F108] ++ L4535 ++ [F211] = L8611 from rfl, show [F108] ++ L4535 = L8607 from rfl,
    show L4535 ++ [F211] = L8609 from rfl] at h
  rw [i5085 hinj, i5083 hinj, i5084 hinj, i2542 hinj] at h
  linarith

theorem row1798 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7302 + (1 : ℝ) * HLm Γ 5 L5767 + (-1 : ℝ) * HLm Γ 5 L8613 + (-1 : ℝ) * HLm Γ 5 L7300 := by
  have h := HLm_submod hΓ [F1] L7301 [F67]
  rw [show [F1] ++ L7301 ++ [F67] = L8614 from rfl, show [F1] ++ L7301 = L7303 from rfl,
    show L7301 ++ [F67] = L8612 from rfl] at h
  rw [i5087 hinj, i4329 hinj, i5086 hinj, i4328 hinj] at h
  linarith

theorem row1799 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8615 + (1 : ℝ) * HLm Γ 5 L8617 + (-1 : ℝ) * HLm Γ 5 L8619 + (-1 : ℝ) * HLm Γ 5 L662 := by
  have h := HLm_submod hΓ [F111] L4542 [F67]
  rw [show [F111] ++ L4542 ++ [F67] = L8620 from rfl, show [F111] ++ L4542 = L8616 from rfl,
    show L4542 ++ [F67] = L8618 from rfl] at h
  rw [i5090 hinj, i5088 hinj, i5089 hinj, i2546 hinj] at h
  linarith

end EntropyBounds.TwoSet.Certs.R7A5
