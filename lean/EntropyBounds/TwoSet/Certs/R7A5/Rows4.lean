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

theorem row600 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L2833 := by
  have h := HLm_mono Γ L2834 [F0]
  rw [show L2834 ++ [F0] = L2832 from rfl] at h
  rw [i1626 hinj, i1627 hinj] at h
  linarith

theorem row601 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L15 + (1 : ℝ) * HLm Γ 5 L5 + (-1 : ℝ) * HLm Γ 5 L623 := by
  have h := HLm_submod hΓ [F7] ([] : List (Form 5)) [F3]
  rw [show [F7] ++ ([] : List (Form 5)) ++ [F3] = L623 from rfl, show [F7] ++ ([] : List (Form 5)) = L15 from rfl,
    show ([] : List (Form 5)) ++ [F3] = L5 from rfl] at h
  rw [HLm_nil (m := 5) hΓ] at h
  linarith

theorem row602 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3 + (1 : ℝ) * HLm Γ 5 L63 + (-1 : ℝ) * HLm Γ 5 L126 := by
  have h := HLm_submod hΓ [F2] ([] : List (Form 5)) [F27]
  rw [show [F2] ++ ([] : List (Form 5)) ++ [F27] = L2835 from rfl, show [F2] ++ ([] : List (Form 5)) = L3 from rfl,
    show ([] : List (Form 5)) ++ [F27] = L63 from rfl] at h
  rw [i1628 hinj, HLm_nil (m := 5) hΓ] at h
  linarith

theorem row603 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L147 + (1 : ℝ) * HLm Γ 5 L2836 + (-1 : ℝ) * HLm Γ 5 L2837 := by
  have h := HLm_submod hΓ [F47] ([] : List (Form 5)) [F217]
  rw [show [F47] ++ ([] : List (Form 5)) ++ [F217] = L2837 from rfl, show [F47] ++ ([] : List (Form 5)) = L147 from rfl,
    show ([] : List (Form 5)) ++ [F217] = L2836 from rfl] at h
  rw [HLm_nil (m := 5) hΓ] at h
  linarith

theorem row604 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L26 + (1 : ℝ) * HLm Γ 5 L2838 + (-1 : ℝ) * HLm Γ 5 L2839 := by
  have h := HLm_submod hΓ [F10] ([] : List (Form 5)) [F218]
  rw [show [F10] ++ ([] : List (Form 5)) ++ [F218] = L2840 from rfl, show [F10] ++ ([] : List (Form 5)) = L27 from rfl,
    show ([] : List (Form 5)) ++ [F218] = L2838 from rfl] at h
  rw [i1629 hinj, i5 hinj, HLm_nil (m := 5) hΓ] at h
  linarith

theorem row605 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1966 + (1 : ℝ) * HLm Γ 5 L456 + (-1 : ℝ) * HLm Γ 5 L2841 := by
  have h := HLm_submod hΓ [F111] ([] : List (Form 5)) [F45]
  rw [show [F111] ++ ([] : List (Form 5)) ++ [F45] = L2841 from rfl, show [F111] ++ ([] : List (Form 5)) = L1966 from rfl,
    show ([] : List (Form 5)) ++ [F45] = L456 from rfl] at h
  rw [HLm_nil (m := 5) hΓ] at h
  linarith

theorem row606 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2842 + (1 : ℝ) * HLm Γ 5 L2838 + (-1 : ℝ) * HLm Γ 5 L2844 := by
  have h := HLm_submod hΓ [F107] ([] : List (Form 5)) [F218]
  rw [show [F107] ++ ([] : List (Form 5)) ++ [F218] = L2845 from rfl, show [F107] ++ ([] : List (Form 5)) = L2843 from rfl,
    show ([] : List (Form 5)) ++ [F218] = L2838 from rfl] at h
  rw [i1631 hinj, i1630 hinj, HLm_nil (m := 5) hΓ] at h
  linarith

theorem row607 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L204 + (1 : ℝ) * HLm Γ 5 L2836 + (-1 : ℝ) * HLm Γ 5 L2846 := by
  have h := HLm_submod hΓ [F46] ([] : List (Form 5)) [F217]
  rw [show [F46] ++ ([] : List (Form 5)) ++ [F217] = L2846 from rfl, show [F46] ++ ([] : List (Form 5)) = L204 from rfl,
    show ([] : List (Form 5)) ++ [F217] = L2836 from rfl] at h
  rw [HLm_nil (m := 5) hΓ] at h
  linarith

theorem row608 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L204 + (1 : ℝ) * HLm Γ 5 L1958 + (-1 : ℝ) * HLm Γ 5 L2847 := by
  have h := HLm_submod hΓ [F46] ([] : List (Form 5)) [F43]
  rw [show [F46] ++ ([] : List (Form 5)) ++ [F43] = L2847 from rfl, show [F46] ++ ([] : List (Form 5)) = L204 from rfl,
    show ([] : List (Form 5)) ++ [F43] = L1958 from rfl] at h
  rw [HLm_nil (m := 5) hΓ] at h
  linarith

theorem row609 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2848 + (1 : ℝ) * HLm Γ 5 L72 + (-1 : ℝ) * HLm Γ 5 L390 := by
  have h := HLm_submod hΓ [F67] ([] : List (Form 5)) [F33]
  rw [show [F67] ++ ([] : List (Form 5)) ++ [F33] = L2849 from rfl, show [F67] ++ ([] : List (Form 5)) = L2848 from rfl,
    show ([] : List (Form 5)) ++ [F33] = L72 from rfl] at h
  rw [i1632 hinj, HLm_nil (m := 5) hΓ] at h
  linarith

theorem row610 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2850 + (1 : ℝ) * HLm Γ 5 L332 + (-1 : ℝ) * HLm Γ 5 L2851 := by
  have h := HLm_submod hΓ [F68] ([] : List (Form 5)) [F86]
  rw [show [F68] ++ ([] : List (Form 5)) ++ [F86] = L2852 from rfl, show [F68] ++ ([] : List (Form 5)) = L2850 from rfl,
    show ([] : List (Form 5)) ++ [F86] = L332 from rfl] at h
  rw [i1633 hinj, HLm_nil (m := 5) hΓ] at h
  linarith

theorem row611 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2850 + (1 : ℝ) * HLm Γ 5 L72 + (-1 : ℝ) * HLm Γ 5 L2853 := by
  have h := HLm_submod hΓ [F68] ([] : List (Form 5)) [F33]
  rw [show [F68] ++ ([] : List (Form 5)) ++ [F33] = L2854 from rfl, show [F68] ++ ([] : List (Form 5)) = L2850 from rfl,
    show ([] : List (Form 5)) ++ [F33] = L72 from rfl] at h
  rw [i1634 hinj, HLm_nil (m := 5) hΓ] at h
  linarith

theorem row612 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L54 + (1 : ℝ) * HLm Γ 5 L332 + (-1 : ℝ) * HLm Γ 5 L2855 := by
  have h := HLm_submod hΓ [F23] ([] : List (Form 5)) [F86]
  rw [show [F23] ++ ([] : List (Form 5)) ++ [F86] = L2856 from rfl, show [F23] ++ ([] : List (Form 5)) = L54 from rfl,
    show ([] : List (Form 5)) ++ [F86] = L332 from rfl] at h
  rw [i1635 hinj, HLm_nil (m := 5) hΓ] at h
  linarith

theorem row613 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L59 + (1 : ℝ) * HLm Γ 5 L456 + (-1 : ℝ) * HLm Γ 5 L452 := by
  have h := HLm_submod hΓ [F25] ([] : List (Form 5)) [F45]
  rw [show [F25] ++ ([] : List (Form 5)) ++ [F45] = L452 from rfl, show [F25] ++ ([] : List (Form 5)) = L59 from rfl,
    show ([] : List (Form 5)) ++ [F45] = L456 from rfl] at h
  rw [HLm_nil (m := 5) hΓ] at h
  linarith

theorem row614 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L59 + (1 : ℝ) * HLm Γ 5 L2836 + (-1 : ℝ) * HLm Γ 5 L2857 := by
  have h := HLm_submod hΓ [F25] ([] : List (Form 5)) [F217]
  rw [show [F25] ++ ([] : List (Form 5)) ++ [F217] = L2857 from rfl, show [F25] ++ ([] : List (Form 5)) = L59 from rfl,
    show ([] : List (Form 5)) ++ [F217] = L2836 from rfl] at h
  rw [HLm_nil (m := 5) hΓ] at h
  linarith

theorem row615 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2010 + (1 : ℝ) * HLm Γ 5 L2858 + (-1 : ℝ) * HLm Γ 5 L2859 + (-1 : ℝ) * HLm Γ 5 L1 := by
  have h := HLm_submod hΓ [F9] L1 [F218]
  rw [show [F9] ++ L1 ++ [F218] = L2859 from rfl, show [F9] ++ L1 = L2010 from rfl,
    show L1 ++ [F218] = L2858 from rfl] at h
  linarith

theorem row616 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2860 + (1 : ℝ) * HLm Γ 5 L2862 + (-1 : ℝ) * HLm Γ 5 L2864 + (-1 : ℝ) * HLm Γ 5 L15 := by
  have h := HLm_submod hΓ [F67] L15 [F33]
  rw [show [F67] ++ L15 ++ [F33] = L2865 from rfl, show [F67] ++ L15 = L2861 from rfl,
    show L15 ++ [F33] = L2863 from rfl] at h
  rw [i1638 hinj, i1636 hinj, i1637 hinj] at h
  linarith

theorem row617 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2866 + (1 : ℝ) * HLm Γ 5 L2867 + (-1 : ℝ) * HLm Γ 5 L2869 + (-1 : ℝ) * HLm Γ 5 L15 := by
  have h := HLm_submod hΓ [F52] L15 [F36]
  rw [show [F52] ++ L15 ++ [F36] = L2870 from rfl, show [F52] ++ L15 = L2866 from rfl,
    show L15 ++ [F36] = L2868 from rfl] at h
  rw [i1640 hinj, i1639 hinj] at h
  linarith

theorem row618 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L114 + (1 : ℝ) * HLm Γ 5 L2872 + (-1 : ℝ) * HLm Γ 5 L2873 + (-1 : ℝ) * HLm Γ 5 L15 := by
  have h := HLm_submod hΓ [F6] L15 [F219]
  rw [show [F6] ++ L15 ++ [F219] = L2874 from rfl, show [F6] ++ L15 = L2871 from rfl,
    show L15 ++ [F219] = L2872 from rfl] at h
  rw [i1642 hinj, i1641 hinj] at h
  linarith

theorem row619 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7 + (1 : ℝ) * HLm Γ 5 L126 + (-1 : ℝ) * HLm Γ 5 L2875 + (-1 : ℝ) * HLm Γ 5 L3 := by
  have h := HLm_submod hΓ [F1] L3 [F27]
  rw [show [F1] ++ L3 ++ [F27] = L2876 from rfl, show [F1] ++ L3 = L7 from rfl,
    show L3 ++ [F27] = L2835 from rfl] at h
  rw [i1643 hinj, i1628 hinj] at h
  linarith

theorem row620 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2877 + (1 : ℝ) * HLm Γ 5 L2879 + (-1 : ℝ) * HLm Γ 5 L2881 + (-1 : ℝ) * HLm Γ 5 L136 := by
  have h := HLm_submod hΓ [F67] L136 [F86]
  rw [show [F67] ++ L136 ++ [F86] = L2882 from rfl, show [F67] ++ L136 = L2878 from rfl,
    show L136 ++ [F86] = L2880 from rfl] at h
  rw [i1646 hinj, i1644 hinj, i1645 hinj] at h
  linarith

theorem row621 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2883 + (1 : ℝ) * HLm Γ 5 L133 + (-1 : ℝ) * HLm Γ 5 L2885 + (-1 : ℝ) * HLm Γ 5 L136 := by
  have h := HLm_submod hΓ [F25] L136 [F45]
  rw [show [F25] ++ L136 ++ [F45] = L2886 from rfl, show [F25] ++ L136 = L2884 from rfl,
    show L136 ++ [F45] = L133 from rfl] at h
  rw [i1648 hinj, i1647 hinj] at h
  linarith

theorem row622 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2 + (1 : ℝ) * HLm Γ 5 L2837 + (-1 : ℝ) * HLm Γ 5 L2888 + (-1 : ℝ) * HLm Γ 5 L147 := by
  have h := HLm_submod hΓ [F0] L147 [F217]
  rw [show [F0] ++ L147 ++ [F217] = L2889 from rfl, show [F0] ++ L147 = L2887 from rfl,
    show L147 ++ [F217] = L2837 from rfl] at h
  rw [i1650 hinj, i1649 hinj] at h
  linarith

theorem row623 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9 + (1 : ℝ) * HLm Γ 5 L2837 + (-1 : ℝ) * HLm Γ 5 L2891 + (-1 : ℝ) * HLm Γ 5 L147 := by
  have h := HLm_submod hΓ [F111] L147 [F217]
  rw [show [F111] ++ L147 ++ [F217] = L2892 from rfl, show [F111] ++ L147 = L2890 from rfl,
    show L147 ++ [F217] = L2837 from rfl] at h
  rw [i1652 hinj, i1651 hinj] at h
  linarith

theorem row624 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2893 + (1 : ℝ) * HLm Γ 5 L2895 + (-1 : ℝ) * HLm Γ 5 L2896 + (-1 : ℝ) * HLm Γ 5 L147 := by
  have h := HLm_submod hΓ [F52] L147 [F34]
  rw [show [F52] ++ L147 ++ [F34] = L2897 from rfl, show [F52] ++ L147 = L2894 from rfl,
    show L147 ++ [F34] = L2895 from rfl] at h
  rw [i1654 hinj, i1653 hinj] at h
  linarith

theorem row625 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L26 + (1 : ℝ) * HLm Γ 5 L2898 + (-1 : ℝ) * HLm Γ 5 L2899 + (-1 : ℝ) * HLm Γ 5 L22 := by
  have h := HLm_submod hΓ [F0] L22 [F219]
  rw [show [F0] ++ L22 ++ [F219] = L2900 from rfl, show [F0] ++ L22 = L154 from rfl,
    show L22 ++ [F219] = L2898 from rfl] at h
  rw [i1655 hinj, i49 hinj] at h
  linarith

theorem row626 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L26 + (1 : ℝ) * HLm Γ 5 L2901 + (-1 : ℝ) * HLm Γ 5 L2839 + (-1 : ℝ) * HLm Γ 5 L22 := by
  have h := HLm_submod hΓ [F0] L22 [F218]
  rw [show [F0] ++ L22 ++ [F218] = L2902 from rfl, show [F0] ++ L22 = L154 from rfl,
    show L22 ++ [F218] = L2901 from rfl] at h
  rw [i1656 hinj, i49 hinj] at h
  linarith

theorem row627 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L307 + (1 : ℝ) * HLm Γ 5 L161 + (-1 : ℝ) * HLm Γ 5 L2904 + (-1 : ℝ) * HLm Γ 5 L22 := by
  have h := HLm_submod hΓ [F16] L22 [F23]
  rw [show [F16] ++ L22 ++ [F23] = L2905 from rfl, show [F16] ++ L22 = L2903 from rfl,
    show L22 ++ [F23] = L161 from rfl] at h
  rw [i1658 hinj, i1657 hinj] at h
  linarith

theorem row628 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2906 + (1 : ℝ) * HLm Γ 5 L155 + (-1 : ℝ) * HLm Γ 5 L790 + (-1 : ℝ) * HLm Γ 5 L22 := by
  have h := HLm_submod hΓ [F67] L22 [F55]
  rw [show [F67] ++ L22 ++ [F55] = L791 from rfl, show [F67] ++ L22 = L2907 from rfl,
    show L22 ++ [F55] = L156 from rfl] at h
  rw [i353 hinj, i1659 hinj, i50 hinj] at h
  linarith

theorem row629 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2908 + (1 : ℝ) * HLm Γ 5 L2910 + (-1 : ℝ) * HLm Γ 5 L2911 + (-1 : ℝ) * HLm Γ 5 L31 := by
  have h := HLm_submod hΓ [F107] L31 [F217]
  rw [show [F107] ++ L31 ++ [F217] = L2912 from rfl, show [F107] ++ L31 = L2909 from rfl,
    show L31 ++ [F217] = L2910 from rfl] at h
  rw [i1661 hinj, i1660 hinj] at h
  linarith

theorem row630 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2913 + (1 : ℝ) * HLm Γ 5 L190 + (-1 : ℝ) * HLm Γ 5 L2915 + (-1 : ℝ) * HLm Γ 5 L31 := by
  have h := HLm_submod hΓ [F210] L31 [F6]
  rw [show [F210] ++ L31 ++ [F6] = L2916 from rfl, show [F210] ++ L31 = L2914 from rfl,
    show L31 ++ [F6] = L191 from rfl] at h
  rw [i1663 hinj, i1662 hinj, i66 hinj] at h
  linarith

theorem row631 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4 + (1 : ℝ) * HLm Γ 5 L2918 + (-1 : ℝ) * HLm Γ 5 L2919 + (-1 : ℝ) * HLm Γ 5 L1966 := by
  have h := HLm_submod hΓ [F0] L1966 [F217]
  rw [show [F0] ++ L1966 ++ [F217] = L2920 from rfl, show [F0] ++ L1966 = L2917 from rfl,
    show L1966 ++ [F217] = L2918 from rfl] at h
  rw [i1665 hinj, i1664 hinj] at h
  linarith

theorem row632 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2921 + (1 : ℝ) * HLm Γ 5 L2841 + (-1 : ℝ) * HLm Γ 5 L2923 + (-1 : ℝ) * HLm Γ 5 L1966 := by
  have h := HLm_submod hΓ [F210] L1966 [F45]
  rw [show [F210] ++ L1966 ++ [F45] = L2924 from rfl, show [F210] ++ L1966 = L2922 from rfl,
    show L1966 ++ [F45] = L2841 from rfl] at h
  rw [i1667 hinj, i1666 hinj] at h
  linarith

theorem row633 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2925 + (1 : ℝ) * HLm Γ 5 L2841 + (-1 : ℝ) * HLm Γ 5 L2927 + (-1 : ℝ) * HLm Γ 5 L1966 := by
  have h := HLm_submod hΓ [F211] L1966 [F45]
  rw [show [F211] ++ L1966 ++ [F45] = L2928 from rfl, show [F211] ++ L1966 = L2926 from rfl,
    show L1966 ++ [F45] = L2841 from rfl] at h
  rw [i1669 hinj, i1668 hinj] at h
  linarith

theorem row634 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2929 + (1 : ℝ) * HLm Γ 5 L2844 + (-1 : ℝ) * HLm Γ 5 L2931 + (-1 : ℝ) * HLm Γ 5 L2842 := by
  have h := HLm_submod hΓ [F17] L2843 [F218]
  rw [show [F17] ++ L2843 ++ [F218] = L2932 from rfl, show [F17] ++ L2843 = L2930 from rfl,
    show L2843 ++ [F218] = L2845 from rfl] at h
  rw [i1671 hinj, i1670 hinj, i1631 hinj, i1630 hinj] at h
  linarith

theorem row635 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6 + (1 : ℝ) * HLm Γ 5 L2933 + (-1 : ℝ) * HLm Γ 5 L2935 + (-1 : ℝ) * HLm Γ 5 L5 := by
  have h := HLm_submod hΓ [F0] L5 [F43]
  rw [show [F0] ++ L5 ++ [F43] = L2936 from rfl, show [F0] ++ L5 = L6 from rfl,
    show L5 ++ [F43] = L2934 from rfl] at h
  rw [i1673 hinj, i1672 hinj] at h
  linarith

theorem row636 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6 + (1 : ℝ) * HLm Γ 5 L2937 + (-1 : ℝ) * HLm Γ 5 L2939 + (-1 : ℝ) * HLm Γ 5 L5 := by
  have h := HLm_submod hΓ [F0] L5 [F219]
  rw [show [F0] ++ L5 ++ [F219] = L2940 from rfl, show [F0] ++ L5 = L6 from rfl,
    show L5 ++ [F219] = L2938 from rfl] at h
  rw [i1675 hinj, i1674 hinj] at h
  linarith

theorem row637 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2037 + (1 : ℝ) * HLm Γ 5 L2942 + (-1 : ℝ) * HLm Γ 5 L2944 + (-1 : ℝ) * HLm Γ 5 L199 := by
  have h := HLm_submod hΓ [F67] L199 [F96]
  rw [show [F67] ++ L199 ++ [F96] = L2945 from rfl, show [F67] ++ L199 = L2941 from rfl,
    show L199 ++ [F96] = L2943 from rfl] at h
  rw [i1678 hinj, i1676 hinj, i1677 hinj] at h
  linarith

theorem row638 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L99 + (1 : ℝ) * HLm Γ 5 L210 + (-1 : ℝ) * HLm Γ 5 L2200 + (-1 : ℝ) * HLm Γ 5 L204 := by
  have h := HLm_submod hΓ [F0] L204 [F16]
  rw [show [F0] ++ L204 ++ [F16] = L2200 from rfl, show [F0] ++ L204 = L99 from rfl,
    show L204 ++ [F16] = L210 from rfl] at h
  linarith

theorem row639 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2946 + (1 : ℝ) * HLm Γ 5 L2948 + (-1 : ℝ) * HLm Γ 5 L2950 + (-1 : ℝ) * HLm Γ 5 L204 := by
  have h := HLm_submod hΓ [F1] L204 [F218]
  rw [show [F1] ++ L204 ++ [F218] = L2951 from rfl, show [F1] ++ L204 = L2947 from rfl,
    show L204 ++ [F218] = L2949 from rfl] at h
  rw [i1681 hinj, i1679 hinj, i1680 hinj] at h
  linarith

theorem row640 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2952 + (1 : ℝ) * HLm Γ 5 L206 + (-1 : ℝ) * HLm Γ 5 L2955 + (-1 : ℝ) * HLm Γ 5 L204 := by
  have h := HLm_submod hΓ [F210] L204 [F6]
  rw [show [F210] ++ L204 ++ [F6] = L2956 from rfl, show [F210] ++ L204 = L2953 from rfl,
    show L204 ++ [F6] = L2954 from rfl] at h
  rw [i1684 hinj, i1682 hinj, i1683 hinj] at h
  linarith

theorem row641 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2957 + (1 : ℝ) * HLm Γ 5 L2846 + (-1 : ℝ) * HLm Γ 5 L2959 + (-1 : ℝ) * HLm Γ 5 L204 := by
  have h := HLm_submod hΓ [F17] L204 [F217]
  rw [show [F17] ++ L204 ++ [F217] = L2960 from rfl, show [F17] ++ L204 = L2958 from rfl,
    show L204 ++ [F217] = L2846 from rfl] at h
  rw [i1686 hinj, i1685 hinj] at h
  linarith

theorem row642 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L349 + (1 : ℝ) * HLm Γ 5 L2962 + (-1 : ℝ) * HLm Γ 5 L2963 + (-1 : ℝ) * HLm Γ 5 L51 := by
  have h := HLm_submod hΓ [F2] L51 [F67]
  rw [show [F2] ++ L51 ++ [F67] = L2964 from rfl, show [F2] ++ L51 = L2961 from rfl,
    show L51 ++ [F67] = L2962 from rfl] at h
  rw [i1688 hinj, i1687 hinj] at h
  linarith

theorem row643 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2962 + (1 : ℝ) * HLm Γ 5 L2084 + (-1 : ℝ) * HLm Γ 5 L2966 + (-1 : ℝ) * HLm Γ 5 L51 := by
  have h := HLm_submod hΓ [F67] L51 [F25]
  rw [show [F67] ++ L51 ++ [F25] = L2967 from rfl, show [F67] ++ L51 = L2965 from rfl,
    show L51 ++ [F25] = L2084 from rfl] at h
  rw [i1690 hinj, i1689 hinj] at h
  linarith

theorem row644 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L576 + (1 : ℝ) * HLm Γ 5 L55 + (-1 : ℝ) * HLm Γ 5 L2241 + (-1 : ℝ) * HLm Γ 5 L53 := by
  have h := HLm_submod hΓ [F10] L53 [F23]
  rw [show [F10] ++ L53 ++ [F23] = L2969 from rfl, show [F10] ++ L53 = L2968 from rfl,
    show L53 ++ [F23] = L55 from rfl] at h
  rw [i1692 hinj, i1691 hinj] at h
  linarith

theorem row645 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L89 + (1 : ℝ) * HLm Γ 5 L2971 + (-1 : ℝ) * HLm Γ 5 L831 + (-1 : ℝ) * HLm Γ 5 L11 := by
  have h := HLm_submod hΓ [F10] L11 [F43]
  rw [show [F10] ++ L11 ++ [F43] = L2973 from rfl, show [F10] ++ L11 = L2970 from rfl,
    show L11 ++ [F43] = L2972 from rfl] at h
  rw [i1695 hinj, i1693 hinj, i1694 hinj] at h
  linarith

theorem row646 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2974 + (1 : ℝ) * HLm Γ 5 L2976 + (-1 : ℝ) * HLm Γ 5 L2978 + (-1 : ℝ) * HLm Γ 5 L11 := by
  have h := HLm_submod hΓ [F44] L11 [F218]
  rw [show [F44] ++ L11 ++ [F218] = L2979 from rfl, show [F44] ++ L11 = L2975 from rfl,
    show L11 ++ [F218] = L2977 from rfl] at h
  rw [i1698 hinj, i1696 hinj, i1697 hinj] at h
  linarith

theorem row647 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2980 + (1 : ℝ) * HLm Γ 5 L329 + (-1 : ℝ) * HLm Γ 5 L2983 + (-1 : ℝ) * HLm Γ 5 L2848 := by
  have h := HLm_submod hΓ [F210] L2848 [F86]
  rw [show [F210] ++ L2848 ++ [F86] = L2984 from rfl, show [F210] ++ L2848 = L2981 from rfl,
    show L2848 ++ [F86] = L2982 from rfl] at h
  rw [i1701 hinj, i1699 hinj, i1700 hinj] at h
  linarith

theorem row648 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2985 + (1 : ℝ) * HLm Γ 5 L2126 + (-1 : ℝ) * HLm Γ 5 L2987 + (-1 : ℝ) * HLm Γ 5 L2848 := by
  have h := HLm_submod hΓ [F214] L2848 [F34]
  rw [show [F214] ++ L2848 ++ [F34] = L2988 from rfl, show [F214] ++ L2848 = L2985 from rfl,
    show L2848 ++ [F34] = L2986 from rfl] at h
  rw [i1703 hinj, i1702 hinj] at h
  linarith

theorem row649 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L329 + (1 : ℝ) * HLm Γ 5 L384 + (-1 : ℝ) * HLm Γ 5 L2990 + (-1 : ℝ) * HLm Γ 5 L2848 := by
  have h := HLm_submod hΓ [F86] L2848 [F90]
  rw [show [F86] ++ L2848 ++ [F90] = L2991 from rfl, show [F86] ++ L2848 = L329 from rfl,
    show L2848 ++ [F90] = L2989 from rfl] at h
  rw [i1705 hinj, i1704 hinj] at h
  linarith

theorem row650 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2992 + (1 : ℝ) * HLm Γ 5 L2994 + (-1 : ℝ) * HLm Γ 5 L2996 + (-1 : ℝ) * HLm Γ 5 L2998 := by
  have h := HLm_submod hΓ [F228] L2998 [F86]
  rw [show [F228] ++ L2998 ++ [F86] = L2997 from rfl, show [F228] ++ L2998 = L2993 from rfl,
    show L2998 ++ [F86] = L2995 from rfl] at h
  rw [i1708 hinj, i1706 hinj, i1707 hinj] at h
  linarith

theorem row651 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2999 + (1 : ℝ) * HLm Γ 5 L3001 + (-1 : ℝ) * HLm Γ 5 L3003 + (-1 : ℝ) * HLm Γ 5 L2850 := by
  have h := HLm_submod hΓ [F9] L2850 [F55]
  rw [show [F9] ++ L2850 ++ [F55] = L3004 from rfl, show [F9] ++ L2850 = L3000 from rfl,
    show L2850 ++ [F55] = L3002 from rfl] at h
  rw [i1711 hinj, i1709 hinj, i1710 hinj] at h
  linarith

theorem row652 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3005 + (1 : ℝ) * HLm Γ 5 L2855 + (-1 : ℝ) * HLm Γ 5 L3007 + (-1 : ℝ) * HLm Γ 5 L54 := by
  have h := HLm_submod hΓ [F214] L54 [F86]
  rw [show [F214] ++ L54 ++ [F86] = L3008 from rfl, show [F214] ++ L54 = L3006 from rfl,
    show L54 ++ [F86] = L2856 from rfl] at h
  rw [i1713 hinj, i1712 hinj, i1635 hinj] at h
  linarith

theorem row653 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3009 + (1 : ℝ) * HLm Γ 5 L3011 + (-1 : ℝ) * HLm Γ 5 L3012 + (-1 : ℝ) * HLm Γ 5 L3014 := by
  have h := HLm_submod hΓ [F10] L3014 [F6]
  rw [show [F10] ++ L3014 ++ [F6] = L3013 from rfl, show [F10] ++ L3014 = L3010 from rfl,
    show L3014 ++ [F6] = L3011 from rfl] at h
  rw [i1715 hinj, i1714 hinj] at h
  linarith

theorem row654 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3015 + (1 : ℝ) * HLm Γ 5 L3017 + (-1 : ℝ) * HLm Γ 5 L3019 + (-1 : ℝ) * HLm Γ 5 L39 := by
  have h := HLm_submod hΓ [F67] L39 [F90]
  rw [show [F67] ++ L39 ++ [F90] = L3020 from rfl, show [F67] ++ L39 = L3016 from rfl,
    show L39 ++ [F90] = L3018 from rfl] at h
  rw [i1718 hinj, i1716 hinj, i1717 hinj] at h
  linarith

theorem row655 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3021 + (1 : ℝ) * HLm Γ 5 L3017 + (-1 : ℝ) * HLm Γ 5 L3023 + (-1 : ℝ) * HLm Γ 5 L39 := by
  have h := HLm_submod hΓ [F52] L39 [F90]
  rw [show [F52] ++ L39 ++ [F90] = L3024 from rfl, show [F52] ++ L39 = L3022 from rfl,
    show L39 ++ [F90] = L3018 from rfl] at h
  rw [i1720 hinj, i1719 hinj, i1717 hinj] at h
  linarith

theorem row656 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2362 + (1 : ℝ) * HLm Γ 5 L2857 + (-1 : ℝ) * HLm Γ 5 L3025 + (-1 : ℝ) * HLm Γ 5 L59 := by
  have h := HLm_submod hΓ [F12] L59 [F217]
  rw [show [F12] ++ L59 ++ [F217] = L3025 from rfl, show [F12] ++ L59 = L2362 from rfl,
    show L59 ++ [F217] = L2857 from rfl] at h
  linarith

theorem row657 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3026 + (1 : ℝ) * HLm Γ 5 L3028 + (-1 : ℝ) * HLm Γ 5 L3030 + (-1 : ℝ) * HLm Γ 5 L59 := by
  have h := HLm_submod hΓ [F107] L59 [F218]
  rw [show [F107] ++ L59 ++ [F218] = L3031 from rfl, show [F107] ++ L59 = L3027 from rfl,
    show L59 ++ [F218] = L3029 from rfl] at h
  rw [i1723 hinj, i1721 hinj, i1722 hinj] at h
  linarith

theorem row658 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3032 + (1 : ℝ) * HLm Γ 5 L452 + (-1 : ℝ) * HLm Γ 5 L3034 + (-1 : ℝ) * HLm Γ 5 L59 := by
  have h := HLm_submod hΓ [F3] L59 [F45]
  rw [show [F3] ++ L59 ++ [F45] = L3035 from rfl, show [F3] ++ L59 = L3033 from rfl,
    show L59 ++ [F45] = L452 from rfl] at h
  rw [i1725 hinj, i1724 hinj] at h
  linarith

theorem row659 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3036 + (1 : ℝ) * HLm Γ 5 L452 + (-1 : ℝ) * HLm Γ 5 L3038 + (-1 : ℝ) * HLm Γ 5 L59 := by
  have h := HLm_submod hΓ [F210] L59 [F45]
  rw [show [F210] ++ L59 ++ [F45] = L3039 from rfl, show [F210] ++ L59 = L3037 from rfl,
    show L59 ++ [F45] = L452 from rfl] at h
  rw [i1727 hinj, i1726 hinj] at h
  linarith

theorem row660 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L233 + (1 : ℝ) * HLm Γ 5 L297 + (-1 : ℝ) * HLm Γ 5 L2286 + (-1 : ℝ) * HLm Γ 5 L63 := by
  have h := HLm_submod hΓ [F0] L63 [F1]
  rw [show [F0] ++ L63 ++ [F1] = L3040 from rfl, show [F0] ++ L63 = L293 from rfl,
    show L63 ++ [F1] = L297 from rfl] at h
  rw [i1728 hinj, i112 hinj] at h
  linarith

theorem row661 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L297 + (1 : ℝ) * HLm Γ 5 L307 + (-1 : ℝ) * HLm Γ 5 L2306 + (-1 : ℝ) * HLm Γ 5 L63 := by
  have h := HLm_submod hΓ [F1] L63 [F9]
  rw [show [F1] ++ L63 ++ [F9] = L3042 from rfl, show [F1] ++ L63 = L298 from rfl,
    show L63 ++ [F9] = L3041 from rfl] at h
  rw [i1730 hinj, i114 hinj, i1729 hinj] at h
  linarith

theorem row662 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L312 + (1 : ℝ) * HLm Γ 5 L3043 + (-1 : ℝ) * HLm Γ 5 L3045 + (-1 : ℝ) * HLm Γ 5 L63 := by
  have h := HLm_submod hΓ [F3] L63 [F217]
  rw [show [F3] ++ L63 ++ [F217] = L3046 from rfl, show [F3] ++ L63 = L313 from rfl,
    show L63 ++ [F217] = L3044 from rfl] at h
  rw [i1732 hinj, i121 hinj, i1731 hinj] at h
  linarith

theorem row663 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L294 + (1 : ℝ) * HLm Γ 5 L323 + (-1 : ℝ) * HLm Γ 5 L3048 + (-1 : ℝ) * HLm Γ 5 L63 := by
  have h := HLm_submod hΓ [F23] L63 [F85]
  rw [show [F23] ++ L63 ++ [F85] = L3049 from rfl, show [F23] ++ L63 = L3047 from rfl,
    show L63 ++ [F85] = L1101 from rfl] at h
  rw [i1734 hinj, i1733 hinj, i521 hinj] at h
  linarith

theorem row664 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3050 + (1 : ℝ) * HLm Γ 5 L329 + (-1 : ℝ) * HLm Γ 5 L3052 + (-1 : ℝ) * HLm Γ 5 L332 := by
  have h := HLm_submod hΓ [F12] L332 [F67]
  rw [show [F12] ++ L332 ++ [F67] = L3053 from rfl, show [F12] ++ L332 = L3051 from rfl,
    show L332 ++ [F67] = L329 from rfl] at h
  rw [i1736 hinj, i1735 hinj] at h
  linarith

theorem row665 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3054 + (1 : ℝ) * HLm Γ 5 L329 + (-1 : ℝ) * HLm Γ 5 L3056 + (-1 : ℝ) * HLm Γ 5 L332 := by
  have h := HLm_submod hΓ [F111] L332 [F67]
  rw [show [F111] ++ L332 ++ [F67] = L3057 from rfl, show [F111] ++ L332 = L3055 from rfl,
    show L332 ++ [F67] = L329 from rfl] at h
  rw [i1738 hinj, i1737 hinj] at h
  linarith

theorem row666 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3058 + (1 : ℝ) * HLm Γ 5 L360 + (-1 : ℝ) * HLm Γ 5 L918 + (-1 : ℝ) * HLm Γ 5 L332 := by
  have h := HLm_submod hΓ [F62] L332 [F3]
  rw [show [F62] ++ L332 ++ [F3] = L3061 from rfl, show [F62] ++ L332 = L3059 from rfl,
    show L332 ++ [F3] = L3060 from rfl] at h
  rw [i1741 hinj, i1739 hinj, i1740 hinj] at h
  linarith

theorem row667 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1009 + (1 : ℝ) * HLm Γ 5 L2855 + (-1 : ℝ) * HLm Γ 5 L3063 + (-1 : ℝ) * HLm Γ 5 L332 := by
  have h := HLm_submod hΓ [F22] L332 [F23]
  rw [show [F22] ++ L332 ++ [F23] = L3064 from rfl, show [F22] ++ L332 = L3062 from rfl,
    show L332 ++ [F23] = L2855 from rfl] at h
  rw [i1743 hinj, i1742 hinj] at h
  linarith

theorem row668 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3065 + (1 : ℝ) * HLm Γ 5 L3067 + (-1 : ℝ) * HLm Γ 5 L3069 + (-1 : ℝ) * HLm Γ 5 L332 := by
  have h := HLm_submod hΓ [F210] L332 [F43]
  rw [show [F210] ++ L332 ++ [F43] = L3070 from rfl, show [F210] ++ L332 = L3066 from rfl,
    show L332 ++ [F43] = L3068 from rfl] at h
  rw [i1746 hinj, i1744 hinj, i1745 hinj] at h
  linarith

theorem row669 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3071 + (1 : ℝ) * HLm Γ 5 L3073 + (-1 : ℝ) * HLm Γ 5 L3074 + (-1 : ℝ) * HLm Γ 5 L332 := by
  have h := HLm_submod hΓ [F228] L332 [F6]
  rw [show [F228] ++ L332 ++ [F6] = L3075 from rfl, show [F228] ++ L332 = L3072 from rfl,
    show L332 ++ [F6] = L3073 from rfl] at h
  rw [i1748 hinj, i1747 hinj] at h
  linarith

theorem row670 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L344 + (1 : ℝ) * HLm Γ 5 L356 + (-1 : ℝ) * HLm Γ 5 L1123 + (-1 : ℝ) * HLm Γ 5 L68 := by
  have h := HLm_submod hΓ [F1] L68 [F6]
  rw [show [F1] ++ L68 ++ [F6] = L3077 from rfl, show [F1] ++ L68 = L345 from rfl,
    show L68 ++ [F6] = L3076 from rfl] at h
  rw [i1750 hinj, i136 hinj, i1749 hinj] at h
  linarith

theorem row671 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L724 + (1 : ℝ) * HLm Γ 5 L368 + (-1 : ℝ) * HLm Γ 5 L3078 + (-1 : ℝ) * HLm Γ 5 L68 := by
  have h := HLm_submod hΓ [F51] L68 [F67]
  rw [show [F51] ++ L68 ++ [F67] = L3079 from rfl, show [F51] ++ L68 = L725 from rfl,
    show L68 ++ [F67] = L368 from rfl] at h
  rw [i1751 hinj, i317 hinj] at h
  linarith

theorem row672 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L368 + (1 : ℝ) * HLm Γ 5 L3080 + (-1 : ℝ) * HLm Γ 5 L3081 + (-1 : ℝ) * HLm Γ 5 L68 := by
  have h := HLm_submod hΓ [F67] L68 [F210]
  rw [show [F67] ++ L68 ++ [F210] = L3082 from rfl, show [F67] ++ L68 = L378 from rfl,
    show L68 ++ [F210] = L3080 from rfl] at h
  rw [i1752 hinj, i152 hinj] at h
  linarith

theorem row673 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L368 + (1 : ℝ) * HLm Γ 5 L3083 + (-1 : ℝ) * HLm Γ 5 L3084 + (-1 : ℝ) * HLm Γ 5 L68 := by
  have h := HLm_submod hΓ [F67] L68 [F36]
  rw [show [F67] ++ L68 ++ [F36] = L3085 from rfl, show [F67] ++ L68 = L378 from rfl,
    show L68 ++ [F36] = L3083 from rfl] at h
  rw [i1753 hinj, i152 hinj] at h
  linarith

theorem row674 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3086 + (1 : ℝ) * HLm Γ 5 L384 + (-1 : ℝ) * HLm Γ 5 L3087 + (-1 : ℝ) * HLm Γ 5 L387 := by
  have h := HLm_submod hΓ [F0] L387 [F67]
  rw [show [F0] ++ L387 ++ [F67] = L3087 from rfl, show [F0] ++ L387 = L3086 from rfl,
    show L387 ++ [F67] = L384 from rfl] at h
  linarith

theorem row675 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3088 + (1 : ℝ) * HLm Γ 5 L3090 + (-1 : ℝ) * HLm Γ 5 L1011 + (-1 : ℝ) * HLm Γ 5 L387 := by
  have h := HLm_submod hΓ [F2] L387 [F86]
  rw [show [F2] ++ L387 ++ [F86] = L3092 from rfl, show [F2] ++ L387 = L3089 from rfl,
    show L387 ++ [F86] = L3091 from rfl] at h
  rw [i1756 hinj, i1754 hinj, i1755 hinj] at h
  linarith

theorem row676 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L384 + (1 : ℝ) * HLm Γ 5 L3093 + (-1 : ℝ) * HLm Γ 5 L3094 + (-1 : ℝ) * HLm Γ 5 L387 := by
  have h := HLm_submod hΓ [F67] L387 [F210]
  rw [show [F67] ++ L387 ++ [F210] = L3095 from rfl, show [F67] ++ L387 = L2989 from rfl,
    show L387 ++ [F210] = L3093 from rfl] at h
  rw [i1757 hinj, i1704 hinj] at h
  linarith

theorem row677 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L384 + (1 : ℝ) * HLm Γ 5 L3096 + (-1 : ℝ) * HLm Γ 5 L3098 + (-1 : ℝ) * HLm Γ 5 L387 := by
  have h := HLm_submod hΓ [F67] L387 [F211]
  rw [show [F67] ++ L387 ++ [F211] = L3099 from rfl, show [F67] ++ L387 = L2989 from rfl,
    show L387 ++ [F211] = L3097 from rfl] at h
  rw [i1759 hinj, i1704 hinj, i1758 hinj] at h
  linarith

theorem row678 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3100 + (1 : ℝ) * HLm Γ 5 L3101 + (-1 : ℝ) * HLm Γ 5 L3102 + (-1 : ℝ) * HLm Γ 5 L387 := by
  have h := HLm_submod hΓ [F52] L387 [F236]
  rw [show [F52] ++ L387 ++ [F236] = L3102 from rfl, show [F52] ++ L387 = L3100 from rfl,
    show L387 ++ [F236] = L3101 from rfl] at h
  linarith

theorem row679 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L344 + (1 : ℝ) * HLm Γ 5 L390 + (-1 : ℝ) * HLm Γ 5 L1135 + (-1 : ℝ) * HLm Γ 5 L72 := by
  have h := HLm_submod hΓ [F1] L72 [F67]
  rw [show [F1] ++ L72 ++ [F67] = L3104 from rfl, show [F1] ++ L72 = L3103 from rfl,
    show L72 ++ [F67] = L390 from rfl] at h
  rw [i1761 hinj, i1760 hinj] at h
  linarith

theorem row680 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3105 + (1 : ℝ) * HLm Γ 5 L390 + (-1 : ℝ) * HLm Γ 5 L3107 + (-1 : ℝ) * HLm Γ 5 L72 := by
  have h := HLm_submod hΓ [F51] L72 [F67]
  rw [show [F51] ++ L72 ++ [F67] = L3108 from rfl, show [F51] ++ L72 = L3106 from rfl,
    show L72 ++ [F67] = L390 from rfl] at h
  rw [i1763 hinj, i1762 hinj] at h
  linarith

theorem row681 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2051 + (1 : ℝ) * HLm Γ 5 L390 + (-1 : ℝ) * HLm Γ 5 L3110 + (-1 : ℝ) * HLm Γ 5 L72 := by
  have h := HLm_submod hΓ [F3] L72 [F67]
  rw [show [F3] ++ L72 ++ [F67] = L3111 from rfl, show [F3] ++ L72 = L3109 from rfl,
    show L72 ++ [F67] = L390 from rfl] at h
  rw [i1765 hinj, i1764 hinj] at h
  linarith

theorem row682 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L390 + (1 : ℝ) * HLm Γ 5 L3112 + (-1 : ℝ) * HLm Γ 5 L3114 + (-1 : ℝ) * HLm Γ 5 L72 := by
  have h := HLm_submod hΓ [F67] L72 [F27]
  rw [show [F67] ++ L72 ++ [F27] = L3115 from rfl, show [F67] ++ L72 = L2849 from rfl,
    show L72 ++ [F27] = L3113 from rfl] at h
  rw [i1767 hinj, i1632 hinj, i1766 hinj] at h
  linarith

theorem row683 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L390 + (1 : ℝ) * HLm Γ 5 L3116 + (-1 : ℝ) * HLm Γ 5 L3118 + (-1 : ℝ) * HLm Γ 5 L72 := by
  have h := HLm_submod hΓ [F67] L72 [F86]
  rw [show [F67] ++ L72 ++ [F86] = L3119 from rfl, show [F67] ++ L72 = L2849 from rfl,
    show L72 ++ [F86] = L3117 from rfl] at h
  rw [i1769 hinj, i1632 hinj, i1768 hinj] at h
  linarith

theorem row684 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3120 + (1 : ℝ) * HLm Γ 5 L3122 + (-1 : ℝ) * HLm Γ 5 L3123 + (-1 : ℝ) * HLm Γ 5 L72 := by
  have h := HLm_submod hΓ [F82] L72 [F228]
  rw [show [F82] ++ L72 ++ [F228] = L3124 from rfl, show [F82] ++ L72 = L3121 from rfl,
    show L72 ++ [F228] = L3122 from rfl] at h
  rw [i1771 hinj, i1770 hinj] at h
  linarith

theorem row685 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2895 + (1 : ℝ) * HLm Γ 5 L2126 + (-1 : ℝ) * HLm Γ 5 L3125 + (-1 : ℝ) * HLm Γ 5 L73 := by
  have h := HLm_submod hΓ [F47] L73 [F67]
  rw [show [F47] ++ L73 ++ [F67] = L3125 from rfl, show [F47] ++ L73 = L2895 from rfl,
    show L73 ++ [F67] = L2126 from rfl] at h
  linarith

theorem row686 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L400 + (1 : ℝ) * HLm Γ 5 L3126 + (-1 : ℝ) * HLm Γ 5 L3128 + (-1 : ℝ) * HLm Γ 5 L73 := by
  have h := HLm_submod hΓ [F52] L73 [F214]
  rw [show [F52] ++ L73 ++ [F214] = L3129 from rfl, show [F52] ++ L73 = L400 from rfl,
    show L73 ++ [F214] = L3127 from rfl] at h
  rw [i1773 hinj, i1772 hinj] at h
  linarith

theorem row687 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L393 + (1 : ℝ) * HLm Γ 5 L417 + (-1 : ℝ) * HLm Γ 5 L2210 + (-1 : ℝ) * HLm Γ 5 L420 := by
  have h := HLm_submod hΓ [F0] L420 [F67]
  rw [show [F0] ++ L420 ++ [F67] = L3131 from rfl, show [F0] ++ L420 = L3130 from rfl,
    show L420 ++ [F67] = L417 from rfl] at h
  rw [i1775 hinj, i1774 hinj] at h
  linarith

theorem row688 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L417 + (1 : ℝ) * HLm Γ 5 L3133 + (-1 : ℝ) * HLm Γ 5 L3134 + (-1 : ℝ) * HLm Γ 5 L420 := by
  have h := HLm_submod hΓ [F67] L420 [F210]
  rw [show [F67] ++ L420 ++ [F210] = L3135 from rfl, show [F67] ++ L420 = L3132 from rfl,
    show L420 ++ [F210] = L3133 from rfl] at h
  rw [i1777 hinj, i1776 hinj] at h
  linarith

theorem row689 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L417 + (1 : ℝ) * HLm Γ 5 L3136 + (-1 : ℝ) * HLm Γ 5 L3138 + (-1 : ℝ) * HLm Γ 5 L420 := by
  have h := HLm_submod hΓ [F67] L420 [F86]
  rw [show [F67] ++ L420 ++ [F86] = L3139 from rfl, show [F67] ++ L420 = L3132 from rfl,
    show L420 ++ [F86] = L3137 from rfl] at h
  rw [i1779 hinj, i1776 hinj, i1778 hinj] at h
  linarith

theorem row690 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3140 + (1 : ℝ) * HLm Γ 5 L445 + (-1 : ℝ) * HLm Γ 5 L3143 + (-1 : ℝ) * HLm Γ 5 L427 := by
  have h := HLm_submod hΓ [F43] L428 [F6]
  rw [show [F43] ++ L428 ++ [F6] = L3144 from rfl, show [F43] ++ L428 = L3141 from rfl,
    show L428 ++ [F6] = L3142 from rfl] at h
  rw [i1782 hinj, i1780 hinj, i1781 hinj, i174 hinj] at h
  linarith

theorem row691 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2841 + (1 : ℝ) * HLm Γ 5 L217 + (-1 : ℝ) * HLm Γ 5 L3146 + (-1 : ℝ) * HLm Γ 5 L456 := by
  have h := HLm_submod hΓ [F111] L456 [F16]
  rw [show [F111] ++ L456 ++ [F16] = L3147 from rfl, show [F111] ++ L456 = L2841 from rfl,
    show L456 ++ [F16] = L3145 from rfl] at h
  rw [i1784 hinj, i1783 hinj] at h
  linarith

theorem row692 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2395 + (1 : ℝ) * HLm Γ 5 L217 + (-1 : ℝ) * HLm Γ 5 L2391 + (-1 : ℝ) * HLm Γ 5 L456 := by
  have h := HLm_submod hΓ [F46] L456 [F16]
  rw [show [F46] ++ L456 ++ [F16] = L2392 from rfl, show [F46] ++ L456 = L2395 from rfl,
    show L456 ++ [F16] = L3145 from rfl] at h
  rw [i1316 hinj, i1783 hinj] at h
  linarith

theorem row693 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3148 + (1 : ℝ) * HLm Γ 5 L3150 + (-1 : ℝ) * HLm Γ 5 L3152 + (-1 : ℝ) * HLm Γ 5 L456 := by
  have h := HLm_submod hΓ [F210] L456 [F96]
  rw [show [F210] ++ L456 ++ [F96] = L3153 from rfl, show [F210] ++ L456 = L3149 from rfl,
    show L456 ++ [F96] = L3151 from rfl] at h
  rw [i1787 hinj, i1785 hinj, i1786 hinj] at h
  linarith

theorem row694 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3154 + (1 : ℝ) * HLm Γ 5 L3155 + (-1 : ℝ) * HLm Γ 5 L3157 + (-1 : ℝ) * HLm Γ 5 L456 := by
  have h := HLm_submod hΓ [F228] L456 [F86]
  rw [show [F228] ++ L456 ++ [F86] = L3158 from rfl, show [F228] ++ L456 = L3154 from rfl,
    show L456 ++ [F86] = L3156 from rfl] at h
  rw [i1789 hinj, i1788 hinj] at h
  linarith

theorem row695 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L91 + (1 : ℝ) * HLm Γ 5 L3159 + (-1 : ℝ) * HLm Γ 5 L3160 + (-1 : ℝ) * HLm Γ 5 L1958 := by
  have h := HLm_submod hΓ [F0] L1958 [F2]
  rw [show [F0] ++ L1958 ++ [F2] = L3160 from rfl, show [F0] ++ L1958 = L91 from rfl,
    show L1958 ++ [F2] = L3159 from rfl] at h
  linarith

theorem row696 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3161 + (1 : ℝ) * HLm Γ 5 L3162 + (-1 : ℝ) * HLm Γ 5 L3163 + (-1 : ℝ) * HLm Γ 5 L1958 := by
  have h := HLm_submod hΓ [F7] L1958 [F218]
  rw [show [F7] ++ L1958 ++ [F218] = L3163 from rfl, show [F7] ++ L1958 = L3161 from rfl,
    show L1958 ++ [F218] = L3162 from rfl] at h
  linarith

theorem row697 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3159 + (1 : ℝ) * HLm Γ 5 L3165 + (-1 : ℝ) * HLm Γ 5 L3167 + (-1 : ℝ) * HLm Γ 5 L1958 := by
  have h := HLm_submod hΓ [F2] L1958 [F211]
  rw [show [F2] ++ L1958 ++ [F211] = L3168 from rfl, show [F2] ++ L1958 = L3164 from rfl,
    show L1958 ++ [F211] = L3166 from rfl] at h
  rw [i1792 hinj, i1790 hinj, i1791 hinj] at h
  linarith

theorem row698 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2847 + (1 : ℝ) * HLm Γ 5 L3169 + (-1 : ℝ) * HLm Γ 5 L3171 + (-1 : ℝ) * HLm Γ 5 L1958 := by
  have h := HLm_submod hΓ [F46] L1958 [F16]
  rw [show [F46] ++ L1958 ++ [F16] = L3172 from rfl, show [F46] ++ L1958 = L2847 from rfl,
    show L1958 ++ [F16] = L3170 from rfl] at h
  rw [i1794 hinj, i1793 hinj] at h
  linarith

theorem row699 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3173 + (1 : ℝ) * HLm Γ 5 L3175 + (-1 : ℝ) * HLm Γ 5 L3177 + (-1 : ℝ) * HLm Γ 5 L1958 := by
  have h := HLm_submod hΓ [F210] L1958 [F30]
  rw [show [F210] ++ L1958 ++ [F30] = L3178 from rfl, show [F210] ++ L1958 = L3174 from rfl,
    show L1958 ++ [F30] = L3176 from rfl] at h
  rw [i1797 hinj, i1795 hinj, i1796 hinj] at h
  linarith

theorem row700 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L114 + (1 : ℝ) * HLm Γ 5 L3179 + (-1 : ℝ) * HLm Γ 5 L2579 + (-1 : ℝ) * HLm Γ 5 L13 := by
  have h := HLm_submod hΓ [F7] L13 [F3]
  rw [show [F7] ++ L13 ++ [F3] = L3181 from rfl, show [F7] ++ L13 = L114 from rfl,
    show L13 ++ [F3] = L3180 from rfl] at h
  rw [i1799 hinj, i1798 hinj] at h
  linarith

theorem row701 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L827 + (1 : ℝ) * HLm Γ 5 L3182 + (-1 : ℝ) * HLm Γ 5 L3184 + (-1 : ℝ) * HLm Γ 5 L13 := by
  have h := HLm_submod hΓ [F9] L13 [F219]
  rw [show [F9] ++ L13 ++ [F219] = L3185 from rfl, show [F9] ++ L13 = L827 from rfl,
    show L13 ++ [F219] = L3183 from rfl] at h
  rw [i1801 hinj, i1800 hinj] at h
  linarith

theorem row702 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3186 + (1 : ℝ) * HLm Γ 5 L3011 + (-1 : ℝ) * HLm Γ 5 L3189 + (-1 : ℝ) * HLm Γ 5 L13 := by
  have h := HLm_submod hΓ [F16] L13 [F211]
  rw [show [F16] ++ L13 ++ [F211] = L3190 from rfl, show [F16] ++ L13 = L3187 from rfl,
    show L13 ++ [F211] = L3188 from rfl] at h
  rw [i1804 hinj, i1802 hinj, i1803 hinj] at h
  linarith

theorem row703 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3191 + (1 : ℝ) * HLm Γ 5 L1085 + (-1 : ℝ) * HLm Γ 5 L3194 + (-1 : ℝ) * HLm Γ 5 L13 := by
  have h := HLm_submod hΓ [F210] L13 [F25]
  rw [show [F210] ++ L13 ++ [F25] = L3195 from rfl, show [F210] ++ L13 = L3192 from rfl,
    show L13 ++ [F25] = L3193 from rfl] at h
  rw [i1807 hinj, i1805 hinj, i1806 hinj] at h
  linarith

theorem row704 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3191 + (1 : ℝ) * HLm Γ 5 L3073 + (-1 : ℝ) * HLm Γ 5 L3197 + (-1 : ℝ) * HLm Γ 5 L13 := by
  have h := HLm_submod hΓ [F210] L13 [F86]
  rw [show [F210] ++ L13 ++ [F86] = L3198 from rfl, show [F210] ++ L13 = L3192 from rfl,
    show L13 ++ [F86] = L3196 from rfl] at h
  rw [i1809 hinj, i1805 hinj, i1808 hinj] at h
  linarith

theorem row705 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3199 + (1 : ℝ) * HLm Γ 5 L3200 + (-1 : ℝ) * HLm Γ 5 L3202 + (-1 : ℝ) * HLm Γ 5 L13 := by
  have h := HLm_submod hΓ [F228] L13 [F55]
  rw [show [F228] ++ L13 ++ [F55] = L3203 from rfl, show [F228] ++ L13 = L3199 from rfl,
    show L13 ++ [F55] = L3201 from rfl] at h
  rw [i1811 hinj, i1810 hinj] at h
  linarith

theorem row706 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3204 + (1 : ℝ) * HLm Γ 5 L3162 + (-1 : ℝ) * HLm Γ 5 L3206 + (-1 : ℝ) * HLm Γ 5 L2838 := by
  have h := HLm_submod hΓ [F0] L2838 [F43]
  rw [show [F0] ++ L2838 ++ [F43] = L3207 from rfl, show [F0] ++ L2838 = L3204 from rfl,
    show L2838 ++ [F43] = L3205 from rfl] at h
  rw [i1813 hinj, i1812 hinj] at h
  linarith

theorem row707 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3208 + (1 : ℝ) * HLm Γ 5 L3209 + (-1 : ℝ) * HLm Γ 5 L3211 + (-1 : ℝ) * HLm Γ 5 L2838 := by
  have h := HLm_submod hΓ [F7] L2838 [F108]
  rw [show [F7] ++ L2838 ++ [F108] = L3212 from rfl, show [F7] ++ L2838 = L3208 from rfl,
    show L2838 ++ [F108] = L3210 from rfl] at h
  rw [i1815 hinj, i1814 hinj] at h
  linarith

theorem row708 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3213 + (1 : ℝ) * HLm Γ 5 L3215 + (-1 : ℝ) * HLm Γ 5 L3217 + (-1 : ℝ) * HLm Γ 5 L2838 := by
  have h := HLm_submod hΓ [F3] L2838 [F85]
  rw [show [F3] ++ L2838 ++ [F85] = L3218 from rfl, show [F3] ++ L2838 = L3214 from rfl,
    show L2838 ++ [F85] = L3216 from rfl] at h
  rw [i1818 hinj, i1816 hinj, i1817 hinj] at h
  linarith

theorem row709 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1280 + (1 : ℝ) * HLm Γ 5 L3220 + (-1 : ℝ) * HLm Γ 5 L3222 + (-1 : ℝ) * HLm Γ 5 L6 := by
  have h := HLm_submod hΓ [F16] L6 [F82]
  rw [show [F16] ++ L6 ++ [F82] = L3223 from rfl, show [F16] ++ L6 = L3219 from rfl,
    show L6 ++ [F82] = L3221 from rfl] at h
  rw [i1821 hinj, i1819 hinj, i1820 hinj] at h
  linarith

theorem row710 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3224 + (1 : ℝ) * HLm Γ 5 L3226 + (-1 : ℝ) * HLm Γ 5 L3228 + (-1 : ℝ) * HLm Γ 5 L6 := by
  have h := HLm_submod hΓ [F228] L6 [F6]
  rw [show [F228] ++ L6 ++ [F6] = L3229 from rfl, show [F228] ++ L6 = L3225 from rfl,
    show L6 ++ [F6] = L3227 from rfl] at h
  rw [i1824 hinj, i1822 hinj, i1823 hinj] at h
  linarith

theorem row711 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2200 + (1 : ℝ) * HLm Γ 5 L3230 + (-1 : ℝ) * HLm Γ 5 L3232 + (-1 : ℝ) * HLm Γ 5 L99 := by
  have h := HLm_submod hΓ [F16] L99 [F68]
  rw [show [F16] ++ L99 ++ [F68] = L3233 from rfl, show [F16] ++ L99 = L2201 from rfl,
    show L99 ++ [F68] = L3231 from rfl] at h
  rw [i1826 hinj, i1208 hinj, i1825 hinj] at h
  linarith

theorem row712 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3234 + (1 : ℝ) * HLm Γ 5 L3236 + (-1 : ℝ) * HLm Γ 5 L3237 + (-1 : ℝ) * HLm Γ 5 L233 := by
  have h := HLm_submod hΓ [F2] L233 [F67]
  rw [show [F2] ++ L233 ++ [F67] = L3238 from rfl, show [F2] ++ L233 = L3235 from rfl,
    show L233 ++ [F67] = L3236 from rfl] at h
  rw [i1828 hinj, i1827 hinj] at h
  linarith

theorem row713 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3239 + (1 : ℝ) * HLm Γ 5 L3241 + (-1 : ℝ) * HLm Γ 5 L3243 + (-1 : ℝ) * HLm Γ 5 L3245 := by
  have h := HLm_submod hΓ [F228] L3245 [F33]
  rw [show [F228] ++ L3245 ++ [F33] = L3244 from rfl, show [F228] ++ L3245 = L3240 from rfl,
    show L3245 ++ [F33] = L3242 from rfl] at h
  rw [i1831 hinj, i1829 hinj, i1830 hinj] at h
  linarith

theorem row714 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L89 + (1 : ℝ) * HLm Γ 5 L3247 + (-1 : ℝ) * HLm Γ 5 L3248 + (-1 : ℝ) * HLm Γ 5 L3086 := by
  have h := HLm_submod hΓ [F7] L3086 [F82]
  rw [show [F7] ++ L3086 ++ [F82] = L3249 from rfl, show [F7] ++ L3086 = L3246 from rfl,
    show L3086 ++ [F82] = L3247 from rfl] at h
  rw [i1833 hinj, i1832 hinj] at h
  linarith

theorem row715 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3250 + (1 : ℝ) * HLm Γ 5 L3252 + (-1 : ℝ) * HLm Γ 5 L3254 + (-1 : ℝ) * HLm Γ 5 L3256 := by
  have h := HLm_submod hΓ [F228] L3257 [F6]
  rw [show [F228] ++ L3257 ++ [F6] = L3255 from rfl, show [F228] ++ L3257 = L3251 from rfl,
    show L3257 ++ [F6] = L3253 from rfl] at h
  rw [i1836 hinj, i1834 hinj, i1835 hinj, i1837 hinj] at h
  linarith

theorem row716 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2210 + (1 : ℝ) * HLm Γ 5 L3258 + (-1 : ℝ) * HLm Γ 5 L3259 + (-1 : ℝ) * HLm Γ 5 L393 := by
  have h := HLm_submod hΓ [F67] L393 [F210]
  rw [show [F67] ++ L393 ++ [F210] = L3260 from rfl, show [F67] ++ L393 = L2211 from rfl,
    show L393 ++ [F210] = L3258 from rfl] at h
  rw [i1838 hinj, i1214 hinj] at h
  linarith

theorem row717 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3261 + (1 : ℝ) * HLm Γ 5 L3263 + (-1 : ℝ) * HLm Γ 5 L3265 + (-1 : ℝ) * HLm Γ 5 L393 := by
  have h := HLm_submod hΓ [F68] L393 [F214]
  rw [show [F68] ++ L393 ++ [F214] = L3266 from rfl, show [F68] ++ L393 = L3262 from rfl,
    show L393 ++ [F214] = L3264 from rfl] at h
  rw [i1841 hinj, i1839 hinj, i1840 hinj] at h
  linarith

theorem row718 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L468 + (1 : ℝ) * HLm Γ 5 L3267 + (-1 : ℝ) * HLm Γ 5 L3269 + (-1 : ℝ) * HLm Γ 5 L96 := by
  have h := HLm_submod hΓ [F3] L96 [F228]
  rw [show [F3] ++ L96 ++ [F228] = L3270 from rfl, show [F3] ++ L96 = L594 from rfl,
    show L96 ++ [F228] = L3268 from rfl] at h
  rw [i1843 hinj, i251 hinj, i1842 hinj] at h
  linarith

theorem row719 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3271 + (1 : ℝ) * HLm Γ 5 L3273 + (-1 : ℝ) * HLm Γ 5 L3274 + (-1 : ℝ) * HLm Γ 5 L91 := by
  have h := HLm_submod hΓ [F107] L91 [F210]
  rw [show [F107] ++ L91 ++ [F210] = L3275 from rfl, show [F107] ++ L91 = L3272 from rfl,
    show L91 ++ [F210] = L3273 from rfl] at h
  rw [i1845 hinj, i1844 hinj] at h
  linarith

theorem row720 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L679 + (1 : ℝ) * HLm Γ 5 L3277 + (-1 : ℝ) * HLm Γ 5 L3279 + (-1 : ℝ) * HLm Γ 5 L14 := by
  have h := HLm_submod hΓ [F7] L14 [F214]
  rw [show [F7] ++ L14 ++ [F214] = L3280 from rfl, show [F7] ++ L14 = L3276 from rfl,
    show L14 ++ [F214] = L3278 from rfl] at h
  rw [i1848 hinj, i1846 hinj, i1847 hinj] at h
  linarith

theorem row721 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2839 + (1 : ℝ) * HLm Γ 5 L3282 + (-1 : ℝ) * HLm Γ 5 L3284 + (-1 : ℝ) * HLm Γ 5 L3204 := by
  have h := HLm_submod hΓ [F7] L3204 [F5]
  rw [show [F7] ++ L3204 ++ [F5] = L3285 from rfl, show [F7] ++ L3204 = L3281 from rfl,
    show L3204 ++ [F5] = L3283 from rfl] at h
  rw [i1851 hinj, i1849 hinj, i1850 hinj] at h
  linarith

theorem row722 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L258 + (1 : ℝ) * HLm Γ 5 L3287 + (-1 : ℝ) * HLm Γ 5 L683 + (-1 : ℝ) * HLm Γ 5 L2010 := by
  have h := HLm_submod hΓ [F0] L2011 [F6]
  rw [show [F0] ++ L2011 ++ [F6] = L3289 from rfl, show [F0] ++ L2011 = L3286 from rfl,
    show L2011 ++ [F6] = L3288 from rfl] at h
  rw [i1854 hinj, i1852 hinj, i1853 hinj, i1101 hinj] at h
  linarith

theorem row723 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L565 + (1 : ℝ) * HLm Γ 5 L1079 + (-1 : ℝ) * HLm Γ 5 L731 + (-1 : ℝ) * HLm Γ 5 L2946 := by
  have h := HLm_submod hΓ [F0] L2947 [F6]
  rw [show [F0] ++ L2947 ++ [F6] = L3291 from rfl, show [F0] ++ L2947 = L1248 from rfl,
    show L2947 ++ [F6] = L3290 from rfl] at h
  rw [i1856 hinj, i606 hinj, i1855 hinj, i1679 hinj] at h
  linarith

theorem row724 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3292 + (1 : ℝ) * HLm Γ 5 L3294 + (-1 : ℝ) * HLm Γ 5 L3296 + (-1 : ℝ) * HLm Γ 5 L344 := by
  have h := HLm_submod hΓ [F68] L345 [F214]
  rw [show [F68] ++ L345 ++ [F214] = L3297 from rfl, show [F68] ++ L345 = L3293 from rfl,
    show L345 ++ [F214] = L3295 from rfl] at h
  rw [i1859 hinj, i1857 hinj, i1858 hinj, i136 hinj] at h
  linarith

theorem row725 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3298 + (1 : ℝ) * HLm Γ 5 L3299 + (-1 : ℝ) * HLm Γ 5 L3301 + (-1 : ℝ) * HLm Γ 5 L3303 := by
  have h := HLm_submod hΓ [F7] L3303 [F217]
  rw [show [F7] ++ L3303 ++ [F217] = L3302 from rfl, show [F7] ++ L3303 = L3298 from rfl,
    show L3303 ++ [F217] = L3300 from rfl] at h
  rw [i1861 hinj, i1860 hinj] at h
  linarith

theorem row726 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3304 + (1 : ℝ) * HLm Γ 5 L3305 + (-1 : ℝ) * HLm Γ 5 L3307 + (-1 : ℝ) * HLm Γ 5 L2858 := by
  have h := HLm_submod hΓ [F7] L2858 [F16]
  rw [show [F7] ++ L2858 ++ [F16] = L3308 from rfl, show [F7] ++ L2858 = L3304 from rfl,
    show L2858 ++ [F16] = L3306 from rfl] at h
  rw [i1863 hinj, i1862 hinj] at h
  linarith

theorem row727 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2859 + (1 : ℝ) * HLm Γ 5 L3305 + (-1 : ℝ) * HLm Γ 5 L3309 + (-1 : ℝ) * HLm Γ 5 L2858 := by
  have h := HLm_submod hΓ [F9] L2858 [F16]
  rw [show [F9] ++ L2858 ++ [F16] = L3310 from rfl, show [F9] ++ L2858 = L2859 from rfl,
    show L2858 ++ [F16] = L3306 from rfl] at h
  rw [i1864 hinj, i1862 hinj] at h
  linarith

theorem row728 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1401 + (1 : ℝ) * HLm Γ 5 L3312 + (-1 : ℝ) * HLm Γ 5 L3314 + (-1 : ℝ) * HLm Γ 5 L178 := by
  have h := HLm_submod hΓ [F47] L179 [F217]
  rw [show [F47] ++ L179 ++ [F217] = L3315 from rfl, show [F47] ++ L179 = L3311 from rfl,
    show L179 ++ [F217] = L3313 from rfl] at h
  rw [i1867 hinj, i1865 hinj, i1866 hinj, i61 hinj] at h
  linarith

theorem row729 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L686 + (1 : ℝ) * HLm Γ 5 L1416 + (-1 : ℝ) * HLm Γ 5 L3316 + (-1 : ℝ) * HLm Γ 5 L623 := by
  have h := HLm_submod hΓ [F0] L623 [F108]
  rw [show [F0] ++ L623 ++ [F108] = L3317 from rfl, show [F0] ++ L623 = L686 from rfl,
    show L623 ++ [F108] = L1417 from rfl] at h
  rw [i1868 hinj, i710 hinj] at h
  linarith

theorem row730 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L624 + (1 : ℝ) * HLm Γ 5 L3318 + (-1 : ℝ) * HLm Γ 5 L3319 + (-1 : ℝ) * HLm Γ 5 L623 := by
  have h := HLm_submod hΓ [F51] L623 [F217]
  rw [show [F51] ++ L623 ++ [F217] = L3320 from rfl, show [F51] ++ L623 = L625 from rfl,
    show L623 ++ [F217] = L3318 from rfl] at h
  rw [i1869 hinj, i268 hinj] at h
  linarith

theorem row731 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3321 + (1 : ℝ) * HLm Γ 5 L3323 + (-1 : ℝ) * HLm Γ 5 L3324 + (-1 : ℝ) * HLm Γ 5 L623 := by
  have h := HLm_submod hΓ [F210] L623 [F45]
  rw [show [F210] ++ L623 ++ [F45] = L3325 from rfl, show [F210] ++ L623 = L3322 from rfl,
    show L623 ++ [F45] = L3323 from rfl] at h
  rw [i1871 hinj, i1870 hinj] at h
  linarith

theorem row732 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1215 + (1 : ℝ) * HLm Γ 5 L3327 + (-1 : ℝ) * HLm Γ 5 L3329 + (-1 : ℝ) * HLm Γ 5 L110 := by
  have h := HLm_submod hΓ [F67] L110 [F214]
  rw [show [F67] ++ L110 ++ [F214] = L3330 from rfl, show [F67] ++ L110 = L3326 from rfl,
    show L110 ++ [F214] = L3328 from rfl] at h
  rw [i1874 hinj, i1872 hinj, i1873 hinj] at h
  linarith

theorem row733 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L619 + (1 : ℝ) * HLm Γ 5 L1431 + (-1 : ℝ) * HLm Γ 5 L3333 + (-1 : ℝ) * HLm Γ 5 L303 := by
  have h := HLm_submod hΓ [F3] L635 [F45]
  rw [show [F3] ++ L635 ++ [F45] = L3334 from rfl, show [F3] ++ L635 = L3331 from rfl,
    show L635 ++ [F45] = L3332 from rfl] at h
  rw [i1877 hinj, i1875 hinj, i1876 hinj, i273 hinj] at h
  linarith

theorem row734 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L111 + (1 : ℝ) * HLm Γ 5 L3336 + (-1 : ℝ) * HLm Γ 5 L3337 + (-1 : ℝ) * HLm Γ 5 L3339 := by
  have h := HLm_submod hΓ [F1] L3339 [F67]
  rw [show [F1] ++ L3339 ++ [F67] = L3338 from rfl, show [F1] ++ L3339 = L3335 from rfl,
    show L3339 ++ [F67] = L3336 from rfl] at h
  rw [i1879 hinj, i1878 hinj] at h
  linarith

theorem row735 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L111 + (1 : ℝ) * HLm Γ 5 L3340 + (-1 : ℝ) * HLm Γ 5 L3342 + (-1 : ℝ) * HLm Γ 5 L3339 := by
  have h := HLm_submod hΓ [F1] L3339 [F52]
  rw [show [F1] ++ L3339 ++ [F52] = L3343 from rfl, show [F1] ++ L3339 = L3335 from rfl,
    show L3339 ++ [F52] = L3341 from rfl] at h
  rw [i1881 hinj, i1878 hinj, i1880 hinj] at h
  linarith

theorem row736 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3344 + (1 : ℝ) * HLm Γ 5 L3346 + (-1 : ℝ) * HLm Γ 5 L3348 + (-1 : ℝ) * HLm Γ 5 L640 := by
  have h := HLm_submod hΓ [F67] L640 [F211]
  rw [show [F67] ++ L640 ++ [F211] = L3349 from rfl, show [F67] ++ L640 = L3345 from rfl,
    show L640 ++ [F211] = L3347 from rfl] at h
  rw [i1884 hinj, i1882 hinj, i1883 hinj] at h
  linarith

theorem row737 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3344 + (1 : ℝ) * HLm Γ 5 L3350 + (-1 : ℝ) * HLm Γ 5 L3352 + (-1 : ℝ) * HLm Γ 5 L640 := by
  have h := HLm_submod hΓ [F67] L640 [F214]
  rw [show [F67] ++ L640 ++ [F214] = L3353 from rfl, show [F67] ++ L640 = L3345 from rfl,
    show L640 ++ [F214] = L3351 from rfl] at h
  rw [i1886 hinj, i1882 hinj, i1885 hinj] at h
  linarith

theorem row738 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3354 + (1 : ℝ) * HLm Γ 5 L3350 + (-1 : ℝ) * HLm Γ 5 L3355 + (-1 : ℝ) * HLm Γ 5 L640 := by
  have h := HLm_submod hΓ [F52] L640 [F214]
  rw [show [F52] ++ L640 ++ [F214] = L3356 from rfl, show [F52] ++ L640 = L3354 from rfl,
    show L640 ++ [F214] = L3351 from rfl] at h
  rw [i1887 hinj, i1885 hinj] at h
  linarith

theorem row739 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3346 + (1 : ℝ) * HLm Γ 5 L3357 + (-1 : ℝ) * HLm Γ 5 L3359 + (-1 : ℝ) * HLm Γ 5 L640 := by
  have h := HLm_submod hΓ [F211] L640 [F43]
  rw [show [F211] ++ L640 ++ [F43] = L3360 from rfl, show [F211] ++ L640 = L3346 from rfl,
    show L640 ++ [F43] = L3358 from rfl] at h
  rw [i1889 hinj, i1888 hinj] at h
  linarith

theorem row740 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3361 + (1 : ℝ) * HLm Γ 5 L3362 + (-1 : ℝ) * HLm Γ 5 L3364 + (-1 : ℝ) * HLm Γ 5 L117 := by
  have h := HLm_submod hΓ [F211] L117 [F34]
  rw [show [F211] ++ L117 ++ [F34] = L3365 from rfl, show [F211] ++ L117 = L3361 from rfl,
    show L117 ++ [F34] = L3363 from rfl] at h
  rw [i1891 hinj, i1890 hinj] at h
  linarith

theorem row741 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3366 + (1 : ℝ) * HLm Γ 5 L3367 + (-1 : ℝ) * HLm Γ 5 L3279 + (-1 : ℝ) * HLm Γ 5 L3370 := by
  have h := HLm_submod hΓ [F0] L3370 [F6]
  rw [show [F0] ++ L3370 ++ [F6] = L3369 from rfl, show [F0] ++ L3370 = L3366 from rfl,
    show L3370 ++ [F6] = L3368 from rfl] at h
  rw [i1893 hinj, i1892 hinj] at h
  linarith

theorem row742 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3371 + (1 : ℝ) * HLm Γ 5 L3373 + (-1 : ℝ) * HLm Γ 5 L3375 + (-1 : ℝ) * HLm Γ 5 L3377 := by
  have h := HLm_submod hΓ [F52] L3378 [F236]
  rw [show [F52] ++ L3378 ++ [F236] = L3376 from rfl, show [F52] ++ L3378 = L3372 from rfl,
    show L3378 ++ [F236] = L3374 from rfl] at h
  rw [i1896 hinj, i1894 hinj, i1895 hinj, i1897 hinj] at h
  linarith

theorem row743 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3379 + (1 : ℝ) * HLm Γ 5 L2864 + (-1 : ℝ) * HLm Γ 5 L3382 + (-1 : ℝ) * HLm Γ 5 L2862 := by
  have h := HLm_submod hΓ [F12] L2863 [F67]
  rw [show [F12] ++ L2863 ++ [F67] = L3383 from rfl, show [F12] ++ L2863 = L3380 from rfl,
    show L2863 ++ [F67] = L3381 from rfl] at h
  rw [i1900 hinj, i1898 hinj, i1899 hinj, i1637 hinj] at h
  linarith

theorem row744 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2869 + (1 : ℝ) * HLm Γ 5 L3384 + (-1 : ℝ) * HLm Γ 5 L3386 + (-1 : ℝ) * HLm Γ 5 L2867 := by
  have h := HLm_submod hΓ [F52] L2868 [F236]
  rw [show [F52] ++ L2868 ++ [F236] = L3387 from rfl, show [F52] ++ L2868 = L2870 from rfl,
    show L2868 ++ [F236] = L3385 from rfl] at h
  rw [i1902 hinj, i1640 hinj, i1901 hinj, i1639 hinj] at h
  linarith

theorem row745 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3388 + (1 : ℝ) * HLm Γ 5 L3390 + (-1 : ℝ) * HLm Γ 5 L3392 + (-1 : ℝ) * HLm Γ 5 L3161 := by
  have h := HLm_submod hΓ [F210] L3161 [F30]
  rw [show [F210] ++ L3161 ++ [F30] = L3393 from rfl, show [F210] ++ L3161 = L3389 from rfl,
    show L3161 ++ [F30] = L3391 from rfl] at h
  rw [i1905 hinj, i1903 hinj, i1904 hinj] at h
  linarith

theorem row746 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L679 + (1 : ℝ) * HLm Γ 5 L3394 + (-1 : ℝ) * HLm Γ 5 L3396 + (-1 : ℝ) * HLm Γ 5 L114 := by
  have h := HLm_submod hΓ [F0] L114 [F217]
  rw [show [F0] ++ L114 ++ [F217] = L3397 from rfl, show [F0] ++ L114 = L679 from rfl,
    show L114 ++ [F217] = L3395 from rfl] at h
  rw [i1907 hinj, i1906 hinj] at h
  linarith

theorem row747 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2579 + (1 : ℝ) * HLm Γ 5 L3399 + (-1 : ℝ) * HLm Γ 5 L3401 + (-1 : ℝ) * HLm Γ 5 L114 := by
  have h := HLm_submod hΓ [F3] L114 [F211]
  rw [show [F3] ++ L114 ++ [F211] = L3402 from rfl, show [F3] ++ L114 = L3398 from rfl,
    show L114 ++ [F211] = L3400 from rfl] at h
  rw [i1910 hinj, i1908 hinj, i1909 hinj] at h
  linarith

theorem row748 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2899 + (1 : ℝ) * HLm Γ 5 L3403 + (-1 : ℝ) * HLm Γ 5 L3405 + (-1 : ℝ) * HLm Γ 5 L2872 := by
  have h := HLm_submod hΓ [F0] L2872 [F34]
  rw [show [F0] ++ L2872 ++ [F34] = L3406 from rfl, show [F0] ++ L2872 = L2899 from rfl,
    show L2872 ++ [F34] = L3404 from rfl] at h
  rw [i1912 hinj, i1911 hinj] at h
  linarith

theorem row749 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2839 + (1 : ℝ) * HLm Γ 5 L3407 + (-1 : ℝ) * HLm Γ 5 L3409 + (-1 : ℝ) * HLm Γ 5 L3208 := by
  have h := HLm_submod hΓ [F0] L3208 [F55]
  rw [show [F0] ++ L3208 ++ [F55] = L3410 from rfl, show [F0] ++ L3208 = L2839 from rfl,
    show L3208 ++ [F55] = L3408 from rfl] at h
  rw [i1914 hinj, i1913 hinj] at h
  linarith

end EntropyBounds.TwoSet.Certs.R7A5
