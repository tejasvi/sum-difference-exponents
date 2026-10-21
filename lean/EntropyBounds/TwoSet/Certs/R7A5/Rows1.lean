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

theorem row150 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L691 + (1 : ℝ) * HLm Γ 5 L693 + (-1 : ℝ) * HLm Γ 5 L695 + (-1 : ℝ) * HLm Γ 5 L697 := by
  have h := HLm_submod hΓ [F1] L698 [F24]
  rw [show [F1] ++ L698 ++ [F24] = L696 from rfl, show [F1] ++ L698 = L692 from rfl,
    show L698 ++ [F24] = L694 from rfl] at h
  rw [i304 hinj, i302 hinj, i303 hinj, i305 hinj] at h
  linarith

theorem row151 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L699 + (1 : ℝ) * HLm Γ 5 L701 + (-1 : ℝ) * HLm Γ 5 L703 + (-1 : ℝ) * HLm Γ 5 L705 := by
  have h := HLm_submod hΓ [F16] L706 [F87]
  rw [show [F16] ++ L706 ++ [F87] = L704 from rfl, show [F16] ++ L706 = L700 from rfl,
    show L706 ++ [F87] = L702 from rfl] at h
  rw [i308 hinj, i306 hinj, i307 hinj, i309 hinj] at h
  linarith

theorem row152 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L707 + (1 : ℝ) * HLm Γ 5 L709 + (-1 : ℝ) * HLm Γ 5 L710 + (-1 : ℝ) * HLm Γ 5 L131 := by
  have h := HLm_submod hΓ [F7] L131 [F48]
  rw [show [F7] ++ L131 ++ [F48] = L711 from rfl, show [F7] ++ L131 = L708 from rfl,
    show L131 ++ [F48] = L709 from rfl] at h
  rw [i311 hinj, i310 hinj] at h
  linarith

theorem row153 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L712 + (1 : ℝ) * HLm Γ 5 L714 + (-1 : ℝ) * HLm Γ 5 L715 + (-1 : ℝ) * HLm Γ 5 L717 := by
  have h := HLm_submod hΓ [F2] L717 [F67]
  rw [show [F2] ++ L717 ++ [F67] = L716 from rfl, show [F2] ++ L717 = L713 from rfl,
    show L717 ++ [F67] = L714 from rfl] at h
  rw [i313 hinj, i312 hinj] at h
  linarith

theorem row154 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L718 + (1 : ℝ) * HLm Γ 5 L720 + (-1 : ℝ) * HLm Γ 5 L722 + (-1 : ℝ) * HLm Γ 5 L724 := by
  have h := HLm_submod hΓ [F46] L725 [F82]
  rw [show [F46] ++ L725 ++ [F82] = L723 from rfl, show [F46] ++ L725 = L719 from rfl,
    show L725 ++ [F82] = L721 from rfl] at h
  rw [i316 hinj, i314 hinj, i315 hinj, i317 hinj] at h
  linarith

theorem row155 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L134 + (1 : ℝ) * HLm Γ 5 L726 + (-1 : ℝ) * HLm Γ 5 L728 + (-1 : ℝ) * HLm Γ 5 L133 := by
  have h := HLm_submod hΓ [F46] L133 [F16]
  rw [show [F46] ++ L133 ++ [F16] = L729 from rfl, show [F46] ++ L133 = L135 from rfl,
    show L133 ++ [F16] = L727 from rfl] at h
  rw [i319 hinj, i40 hinj, i318 hinj] at h
  linarith

theorem row156 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L565 + (1 : ℝ) * HLm Γ 5 L208 + (-1 : ℝ) * HLm Γ 5 L731 + (-1 : ℝ) * HLm Γ 5 L205 := by
  have h := HLm_submod hΓ [F0] L205 [F13]
  rw [show [F0] ++ L205 ++ [F13] = L732 from rfl, show [F0] ++ L205 = L730 from rfl,
    show L205 ++ [F13] = L209 from rfl] at h
  rw [i321 hinj, i320 hinj, i73 hinj] at h
  linarith

theorem row157 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L733 + (1 : ℝ) * HLm Γ 5 L735 + (-1 : ℝ) * HLm Γ 5 L737 + (-1 : ℝ) * HLm Γ 5 L739 := by
  have h := HLm_submod hΓ [F2] L740 [F24]
  rw [show [F2] ++ L740 ++ [F24] = L738 from rfl, show [F2] ++ L740 = L734 from rfl,
    show L740 ++ [F24] = L736 from rfl] at h
  rw [i324 hinj, i322 hinj, i323 hinj, i325 hinj] at h
  linarith

theorem row158 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L741 + (1 : ℝ) * HLm Γ 5 L743 + (-1 : ℝ) * HLm Γ 5 L745 + (-1 : ℝ) * HLm Γ 5 L747 := by
  have h := HLm_submod hΓ [F0] L748 [F67]
  rw [show [F0] ++ L748 ++ [F67] = L746 from rfl, show [F0] ++ L748 = L742 from rfl,
    show L748 ++ [F67] = L744 from rfl] at h
  rw [i328 hinj, i326 hinj, i327 hinj, i329 hinj] at h
  linarith

theorem row159 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L749 + (1 : ℝ) * HLm Γ 5 L751 + (-1 : ℝ) * HLm Γ 5 L753 + (-1 : ℝ) * HLm Γ 5 L755 := by
  have h := HLm_submod hΓ [F16] L756 [F117]
  rw [show [F16] ++ L756 ++ [F117] = L754 from rfl, show [F16] ++ L756 = L750 from rfl,
    show L756 ++ [F117] = L752 from rfl] at h
  rw [i332 hinj, i330 hinj, i331 hinj, i333 hinj] at h
  linarith

theorem row160 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L757 + (1 : ℝ) * HLm Γ 5 L759 + (-1 : ℝ) * HLm Γ 5 L761 + (-1 : ℝ) * HLm Γ 5 L159 := by
  have h := HLm_submod hΓ [F52] L763 [F25]
  rw [show [F52] ++ L763 ++ [F25] = L762 from rfl, show [F52] ++ L763 = L758 from rfl,
    show L763 ++ [F25] = L760 from rfl] at h
  rw [i336 hinj, i334 hinj, i335 hinj, i337 hinj] at h
  linarith

theorem row161 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L576 + (1 : ℝ) * HLm Γ 5 L765 + (-1 : ℝ) * HLm Γ 5 L767 + (-1 : ℝ) * HLm Γ 5 L168 := by
  have h := HLm_submod hΓ [F0] L769 [F2]
  rw [show [F0] ++ L769 ++ [F2] = L768 from rfl, show [F0] ++ L769 = L764 from rfl,
    show L769 ++ [F2] = L766 from rfl] at h
  rw [i340 hinj, i338 hinj, i339 hinj, i341 hinj] at h
  linarith

theorem row162 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L770 + (1 : ℝ) * HLm Γ 5 L274 + (-1 : ℝ) * HLm Γ 5 L772 + (-1 : ℝ) * HLm Γ 5 L271 := by
  have h := HLm_submod hΓ [F12] L272 [F45]
  rw [show [F12] ++ L272 ++ [F45] = L773 from rfl, show [F12] ++ L272 = L771 from rfl,
    show L272 ++ [F45] = L275 from rfl] at h
  rw [i343 hinj, i342 hinj, i103 hinj, i102 hinj] at h
  linarith

theorem row163 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L774 + (1 : ℝ) * HLm Γ 5 L776 + (-1 : ℝ) * HLm Γ 5 L778 + (-1 : ℝ) * HLm Γ 5 L172 := by
  have h := HLm_submod hΓ [F1] L780 [F16]
  rw [show [F1] ++ L780 ++ [F16] = L779 from rfl, show [F1] ++ L780 = L775 from rfl,
    show L780 ++ [F16] = L777 from rfl] at h
  rw [i346 hinj, i344 hinj, i345 hinj, i347 hinj] at h
  linarith

theorem row164 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L385 + (1 : ℝ) * HLm Γ 5 L782 + (-1 : ℝ) * HLm Γ 5 L784 + (-1 : ℝ) * HLm Γ 5 L382 := by
  have h := HLm_submod hΓ [F67] L383 [F33]
  rw [show [F67] ++ L383 ++ [F33] = L785 from rfl, show [F67] ++ L383 = L781 from rfl,
    show L383 ++ [F33] = L783 from rfl] at h
  rw [i350 hinj, i348 hinj, i349 hinj, i154 hinj] at h
  linarith

theorem row165 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L157 + (1 : ℝ) * HLm Γ 5 L786 + (-1 : ℝ) * HLm Γ 5 L788 + (-1 : ℝ) * HLm Γ 5 L155 := by
  have h := HLm_submod hΓ [F0] L156 [F96]
  rw [show [F0] ++ L156 ++ [F96] = L789 from rfl, show [F0] ++ L156 = L158 from rfl,
    show L156 ++ [F96] = L787 from rfl] at h
  rw [i352 hinj, i51 hinj, i351 hinj, i50 hinj] at h
  linarith

theorem row166 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L790 + (1 : ℝ) * HLm Γ 5 L792 + (-1 : ℝ) * HLm Γ 5 L794 + (-1 : ℝ) * HLm Γ 5 L155 := by
  have h := HLm_submod hΓ [F67] L156 [F25]
  rw [show [F67] ++ L156 ++ [F25] = L795 from rfl, show [F67] ++ L156 = L791 from rfl,
    show L156 ++ [F25] = L793 from rfl] at h
  rw [i355 hinj, i353 hinj, i354 hinj, i50 hinj] at h
  linarith

theorem row167 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L796 + (1 : ℝ) * HLm Γ 5 L274 + (-1 : ℝ) * HLm Γ 5 L799 + (-1 : ℝ) * HLm Γ 5 L801 := by
  have h := HLm_submod hΓ [F16] L801 [F17]
  rw [show [F16] ++ L801 ++ [F17] = L800 from rfl, show [F16] ++ L801 = L797 from rfl,
    show L801 ++ [F17] = L798 from rfl] at h
  rw [i358 hinj, i356 hinj, i357 hinj] at h
  linarith

theorem row168 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L802 + (1 : ℝ) * HLm Γ 5 L796 + (-1 : ℝ) * HLm Γ 5 L805 + (-1 : ℝ) * HLm Γ 5 L807 := by
  have h := HLm_submod hΓ [F111] L807 [F16]
  rw [show [F111] ++ L807 ++ [F16] = L806 from rfl, show [F111] ++ L807 = L803 from rfl,
    show L807 ++ [F16] = L804 from rfl] at h
  rw [i361 hinj, i359 hinj, i360 hinj] at h
  linarith

theorem row169 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L808 + (1 : ℝ) * HLm Γ 5 L176 + (-1 : ℝ) * HLm Γ 5 L811 + (-1 : ℝ) * HLm Γ 5 L174 := by
  have h := HLm_submod hΓ [F16] L175 [F25]
  rw [show [F16] ++ L175 ++ [F25] = L812 from rfl, show [F16] ++ L175 = L809 from rfl,
    show L175 ++ [F25] = L810 from rfl] at h
  rw [i364 hinj, i362 hinj, i363 hinj, i59 hinj] at h
  linarith

theorem row170 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L813 + (1 : ℝ) * HLm Γ 5 L815 + (-1 : ℝ) * HLm Γ 5 L817 + (-1 : ℝ) * HLm Γ 5 L480 := by
  have h := HLm_submod hΓ [F1] L481 [F21]
  rw [show [F1] ++ L481 ++ [F21] = L818 from rfl, show [F1] ++ L481 = L814 from rfl,
    show L481 ++ [F21] = L816 from rfl] at h
  rw [i367 hinj, i365 hinj, i366 hinj, i200 hinj] at h
  linarith

theorem row171 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L483 + (1 : ℝ) * HLm Γ 5 L815 + (-1 : ℝ) * HLm Γ 5 L820 + (-1 : ℝ) * HLm Γ 5 L480 := by
  have h := HLm_submod hΓ [F3] L481 [F21]
  rw [show [F3] ++ L481 ++ [F21] = L821 from rfl, show [F3] ++ L481 = L819 from rfl,
    show L481 ++ [F21] = L816 from rfl] at h
  rw [i369 hinj, i368 hinj, i366 hinj, i200 hinj] at h
  linarith

theorem row172 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L679 + (1 : ℝ) * HLm Γ 5 L823 + (-1 : ℝ) * HLm Γ 5 L825 + (-1 : ℝ) * HLm Γ 5 L827 := by
  have h := HLm_submod hΓ [F0] L827 [F2]
  rw [show [F0] ++ L827 ++ [F2] = L826 from rfl, show [F0] ++ L827 = L822 from rfl,
    show L827 ++ [F2] = L824 from rfl] at h
  rw [i372 hinj, i370 hinj, i371 hinj] at h
  linarith

theorem row173 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L92 + (1 : ℝ) * HLm Γ 5 L829 + (-1 : ℝ) * HLm Γ 5 L831 + (-1 : ℝ) * HLm Γ 5 L833 := by
  have h := HLm_submod hΓ [F0] L834 [F5]
  rw [show [F0] ++ L834 ++ [F5] = L832 from rfl, show [F0] ++ L834 = L828 from rfl,
    show L834 ++ [F5] = L830 from rfl] at h
  rw [i375 hinj, i373 hinj, i374 hinj, i376 hinj] at h
  linarith

theorem row174 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L679 + (1 : ℝ) * HLm Γ 5 L836 + (-1 : ℝ) * HLm Γ 5 L683 + (-1 : ℝ) * HLm Γ 5 L504 := by
  have h := HLm_submod hΓ [F0] L505 [F1]
  rw [show [F0] ++ L505 ++ [F1] = L838 from rfl, show [F0] ++ L505 = L835 from rfl,
    show L505 ++ [F1] = L837 from rfl] at h
  rw [i379 hinj, i377 hinj, i378 hinj, i209 hinj] at h
  linarith

theorem row175 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L679 + (1 : ℝ) * HLm Γ 5 L506 + (-1 : ℝ) * HLm Γ 5 L839 + (-1 : ℝ) * HLm Γ 5 L504 := by
  have h := HLm_submod hΓ [F0] L505 [F3]
  rw [show [F0] ++ L505 ++ [F3] = L840 from rfl, show [F0] ++ L505 = L835 from rfl,
    show L505 ++ [F3] = L507 from rfl] at h
  rw [i380 hinj, i377 hinj, i210 hinj, i209 hinj] at h
  linarith

theorem row176 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L679 + (1 : ℝ) * HLm Γ 5 L530 + (-1 : ℝ) * HLm Γ 5 L842 + (-1 : ℝ) * HLm Γ 5 L504 := by
  have h := HLm_submod hΓ [F0] L505 [F43]
  rw [show [F0] ++ L505 ++ [F43] = L843 from rfl, show [F0] ++ L505 = L835 from rfl,
    show L505 ++ [F43] = L841 from rfl] at h
  rw [i382 hinj, i377 hinj, i381 hinj, i209 hinj] at h
  linarith

theorem row177 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L825 + (1 : ℝ) * HLm Γ 5 L845 + (-1 : ℝ) * HLm Γ 5 L847 + (-1 : ℝ) * HLm Γ 5 L849 := by
  have h := HLm_submod hΓ [F2] L850 [F16]
  rw [show [F2] ++ L850 ++ [F16] = L848 from rfl, show [F2] ++ L850 = L844 from rfl,
    show L850 ++ [F16] = L846 from rfl] at h
  rw [i385 hinj, i383 hinj, i384 hinj, i386 hinj] at h
  linarith

theorem row178 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L851 + (1 : ℝ) * HLm Γ 5 L188 + (-1 : ℝ) * HLm Γ 5 L842 + (-1 : ℝ) * HLm Γ 5 L183 := by
  have h := HLm_submod hΓ [F51] L183 [F45]
  rw [show [F51] ++ L183 ++ [F45] = L853 from rfl, show [F51] ++ L183 = L852 from rfl,
    show L183 ++ [F45] = L188 from rfl] at h
  rw [i388 hinj, i387 hinj] at h
  linarith

theorem row179 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L854 + (1 : ℝ) * HLm Γ 5 L856 + (-1 : ℝ) * HLm Γ 5 L858 + (-1 : ℝ) * HLm Γ 5 L183 := by
  have h := HLm_submod hΓ [F0] L183 [F13]
  rw [show [F0] ++ L183 ++ [F13] = L859 from rfl, show [F0] ++ L183 = L855 from rfl,
    show L183 ++ [F13] = L857 from rfl] at h
  rw [i391 hinj, i389 hinj, i390 hinj] at h
  linarith

theorem row180 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L860 + (1 : ℝ) * HLm Γ 5 L862 + (-1 : ℝ) * HLm Γ 5 L863 + (-1 : ℝ) * HLm Γ 5 L865 := by
  have h := HLm_submod hΓ [F9] L865 [F67]
  rw [show [F9] ++ L865 ++ [F67] = L864 from rfl, show [F9] ++ L865 = L861 from rfl,
    show L865 ++ [F67] = L862 from rfl] at h
  rw [i393 hinj, i392 hinj] at h
  linarith

theorem row181 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L866 + (1 : ℝ) * HLm Γ 5 L868 + (-1 : ℝ) * HLm Γ 5 L870 + (-1 : ℝ) * HLm Γ 5 L421 := by
  have h := HLm_submod hΓ [F7] L872 [F23]
  rw [show [F7] ++ L872 ++ [F23] = L871 from rfl, show [F7] ++ L872 = L867 from rfl,
    show L872 ++ [F23] = L869 from rfl] at h
  rw [i396 hinj, i394 hinj, i395 hinj, i397 hinj] at h
  linarith

theorem row182 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L873 + (1 : ℝ) * HLm Γ 5 L875 + (-1 : ℝ) * HLm Γ 5 L876 + (-1 : ℝ) * HLm Γ 5 L878 := by
  have h := HLm_submod hΓ [F1] L878 [F67]
  rw [show [F1] ++ L878 ++ [F67] = L877 from rfl, show [F1] ++ L878 = L874 from rfl,
    show L878 ++ [F67] = L875 from rfl] at h
  rw [i399 hinj, i398 hinj] at h
  linarith

theorem row183 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L873 + (1 : ℝ) * HLm Γ 5 L879 + (-1 : ℝ) * HLm Γ 5 L881 + (-1 : ℝ) * HLm Γ 5 L878 := by
  have h := HLm_submod hΓ [F1] L878 [F6]
  rw [show [F1] ++ L878 ++ [F6] = L882 from rfl, show [F1] ++ L878 = L874 from rfl,
    show L878 ++ [F6] = L880 from rfl] at h
  rw [i401 hinj, i398 hinj, i400 hinj] at h
  linarith

theorem row184 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L883 + (1 : ℝ) * HLm Γ 5 L885 + (-1 : ℝ) * HLm Γ 5 L887 + (-1 : ℝ) * HLm Γ 5 L889 := by
  have h := HLm_submod hΓ [F67] L890 [F86]
  rw [show [F67] ++ L890 ++ [F86] = L888 from rfl, show [F67] ++ L890 = L884 from rfl,
    show L890 ++ [F86] = L886 from rfl] at h
  rw [i404 hinj, i402 hinj, i403 hinj, i405 hinj] at h
  linarith

theorem row185 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L891 + (1 : ℝ) * HLm Γ 5 L893 + (-1 : ℝ) * HLm Γ 5 L895 + (-1 : ℝ) * HLm Γ 5 L508 := by
  have h := HLm_submod hΓ [F1] L508 [F22]
  rw [show [F1] ++ L508 ++ [F22] = L896 from rfl, show [F1] ++ L508 = L892 from rfl,
    show L508 ++ [F22] = L894 from rfl] at h
  rw [i408 hinj, i406 hinj, i407 hinj] at h
  linarith

theorem row186 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L897 + (1 : ℝ) * HLm Γ 5 L197 + (-1 : ℝ) * HLm Γ 5 L900 + (-1 : ℝ) * HLm Γ 5 L194 := by
  have h := HLm_submod hΓ [F7] L902 [F45]
  rw [show [F7] ++ L902 ++ [F45] = L901 from rfl, show [F7] ++ L902 = L898 from rfl,
    show L902 ++ [F45] = L899 from rfl] at h
  rw [i411 hinj, i409 hinj, i410 hinj, i412 hinj] at h
  linarith

theorem row187 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L621 + (1 : ℝ) * HLm Γ 5 L369 + (-1 : ℝ) * HLm Γ 5 L904 + (-1 : ℝ) * HLm Γ 5 L366 := by
  have h := HLm_submod hΓ [F62] L367 [F67]
  rw [show [F62] ++ L367 ++ [F67] = L905 from rfl, show [F62] ++ L367 = L903 from rfl,
    show L367 ++ [F67] = L370 from rfl] at h
  rw [i414 hinj, i413 hinj, i147 hinj, i146 hinj] at h
  linarith

theorem row188 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L860 + (1 : ℝ) * HLm Γ 5 L516 + (-1 : ℝ) * HLm Γ 5 L908 + (-1 : ℝ) * HLm Γ 5 L910 := by
  have h := HLm_submod hΓ [F9] L911 [F68]
  rw [show [F9] ++ L911 ++ [F68] = L909 from rfl, show [F9] ++ L911 = L906 from rfl,
    show L911 ++ [F68] = L907 from rfl] at h
  rw [i417 hinj, i415 hinj, i416 hinj, i418 hinj] at h
  linarith

theorem row189 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L912 + (1 : ℝ) * HLm Γ 5 L914 + (-1 : ℝ) * HLm Γ 5 L916 + (-1 : ℝ) * HLm Γ 5 L318 := by
  have h := HLm_submod hΓ [F1] L319 [F38]
  rw [show [F1] ++ L319 ++ [F38] = L917 from rfl, show [F1] ++ L319 = L913 from rfl,
    show L319 ++ [F38] = L915 from rfl] at h
  rw [i421 hinj, i419 hinj, i420 hinj, i124 hinj] at h
  linarith

theorem row190 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L918 + (1 : ℝ) * HLm Γ 5 L920 + (-1 : ℝ) * HLm Γ 5 L922 + (-1 : ℝ) * HLm Γ 5 L318 := by
  have h := HLm_submod hΓ [F62] L319 [F24]
  rw [show [F62] ++ L319 ++ [F24] = L923 from rfl, show [F62] ++ L319 = L919 from rfl,
    show L319 ++ [F24] = L921 from rfl] at h
  rw [i424 hinj, i422 hinj, i423 hinj, i124 hinj] at h
  linarith

theorem row191 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L924 + (1 : ℝ) * HLm Γ 5 L926 + (-1 : ℝ) * HLm Γ 5 L928 + (-1 : ℝ) * HLm Γ 5 L930 := by
  have h := HLm_submod hΓ [F67] L931 [F50]
  rw [show [F67] ++ L931 ++ [F50] = L929 from rfl, show [F67] ++ L931 = L925 from rfl,
    show L931 ++ [F50] = L927 from rfl] at h
  rw [i427 hinj, i425 hinj, i426 hinj, i428 hinj] at h
  linarith

theorem row192 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L932 + (1 : ℝ) * HLm Γ 5 L934 + (-1 : ℝ) * HLm Γ 5 L936 + (-1 : ℝ) * HLm Γ 5 L938 := by
  have h := HLm_submod hΓ [F1] L939 [F16]
  rw [show [F1] ++ L939 ++ [F16] = L937 from rfl, show [F1] ++ L939 = L933 from rfl,
    show L939 ++ [F16] = L935 from rfl] at h
  rw [i431 hinj, i429 hinj, i430 hinj, i432 hinj] at h
  linarith

theorem row193 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L940 + (1 : ℝ) * HLm Γ 5 L402 + (-1 : ℝ) * HLm Γ 5 L942 + (-1 : ℝ) * HLm Γ 5 L398 := by
  have h := HLm_submod hΓ [F2] L399 [F52]
  rw [show [F2] ++ L399 ++ [F52] = L943 from rfl, show [F2] ++ L399 = L941 from rfl,
    show L399 ++ [F52] = L403 from rfl] at h
  rw [i434 hinj, i433 hinj, i162 hinj, i160 hinj] at h
  linarith

theorem row194 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L185 + (1 : ℝ) * HLm Γ 5 L418 + (-1 : ℝ) * HLm Γ 5 L945 + (-1 : ℝ) * HLm Γ 5 L415 := by
  have h := HLm_submod hΓ [F12] L416 [F67]
  rw [show [F12] ++ L416 ++ [F67] = L946 from rfl, show [F12] ++ L416 = L944 from rfl,
    show L416 ++ [F67] = L419 from rfl] at h
  rw [i436 hinj, i435 hinj, i170 hinj, i169 hinj] at h
  linarith

theorem row195 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L947 + (1 : ℝ) * HLm Γ 5 L796 + (-1 : ℝ) * HLm Γ 5 L950 + (-1 : ℝ) * HLm Γ 5 L952 := by
  have h := HLm_submod hΓ [F2] L953 [F9]
  rw [show [F2] ++ L953 ++ [F9] = L951 from rfl, show [F2] ++ L953 = L948 from rfl,
    show L953 ++ [F9] = L949 from rfl] at h
  rw [i439 hinj, i437 hinj, i438 hinj, i440 hinj] at h
  linarith

theorem row196 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L954 + (1 : ℝ) * HLm Γ 5 L956 + (-1 : ℝ) * HLm Γ 5 L957 + (-1 : ℝ) * HLm Γ 5 L227 := by
  have h := HLm_submod hΓ [F0] L227 [F3]
  rw [show [F0] ++ L227 ++ [F3] = L958 from rfl, show [F0] ++ L227 = L955 from rfl,
    show L227 ++ [F3] = L956 from rfl] at h
  rw [i442 hinj, i441 hinj] at h
  linarith

theorem row197 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L959 + (1 : ℝ) * HLm Γ 5 L961 + (-1 : ℝ) * HLm Γ 5 L963 + (-1 : ℝ) * HLm Γ 5 L965 := by
  have h := HLm_submod hΓ [F2] L966 [F68]
  rw [show [F2] ++ L966 ++ [F68] = L964 from rfl, show [F2] ++ L966 = L960 from rfl,
    show L966 ++ [F68] = L962 from rfl] at h
  rw [i445 hinj, i443 hinj, i444 hinj, i446 hinj] at h
  linarith

theorem row198 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L595 + (1 : ℝ) * HLm Γ 5 L968 + (-1 : ℝ) * HLm Γ 5 L970 + (-1 : ℝ) * HLm Γ 5 L972 := by
  have h := HLm_submod hΓ [F0] L973 [F96]
  rw [show [F0] ++ L973 ++ [F96] = L971 from rfl, show [F0] ++ L973 = L967 from rfl,
    show L973 ++ [F96] = L969 from rfl] at h
  rw [i449 hinj, i447 hinj, i448 hinj, i450 hinj] at h
  linarith

theorem row199 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L166 + (1 : ℝ) * HLm Γ 5 L975 + (-1 : ℝ) * HLm Γ 5 L977 + (-1 : ℝ) * HLm Γ 5 L979 := by
  have h := HLm_submod hΓ [F9] L980 [F29]
  rw [show [F9] ++ L980 ++ [F29] = L978 from rfl, show [F9] ++ L980 = L974 from rfl,
    show L980 ++ [F29] = L976 from rfl] at h
  rw [i453 hinj, i451 hinj, i452 hinj, i454 hinj] at h
  linarith

theorem row200 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L981 + (1 : ℝ) * HLm Γ 5 L231 + (-1 : ℝ) * HLm Γ 5 L984 + (-1 : ℝ) * HLm Γ 5 L229 := by
  have h := HLm_submod hΓ [F2] L230 [F68]
  rw [show [F2] ++ L230 ++ [F68] = L985 from rfl, show [F2] ++ L230 = L982 from rfl,
    show L230 ++ [F68] = L983 from rfl] at h
  rw [i457 hinj, i455 hinj, i456 hinj, i82 hinj] at h
  linarith

theorem row201 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L986 + (1 : ℝ) * HLm Γ 5 L516 + (-1 : ℝ) * HLm Γ 5 L989 + (-1 : ℝ) * HLm Γ 5 L991 := by
  have h := HLm_submod hΓ [F0] L992 [F46]
  rw [show [F0] ++ L992 ++ [F46] = L990 from rfl, show [F0] ++ L992 = L987 from rfl,
    show L992 ++ [F46] = L988 from rfl] at h
  rw [i460 hinj, i458 hinj, i459 hinj, i461 hinj] at h
  linarith

theorem row202 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L993 + (1 : ℝ) * HLm Γ 5 L995 + (-1 : ℝ) * HLm Γ 5 L997 + (-1 : ℝ) * HLm Γ 5 L991 := by
  have h := HLm_submod hΓ [F25] L992 [F26]
  rw [show [F25] ++ L992 ++ [F26] = L998 from rfl, show [F25] ++ L992 = L994 from rfl,
    show L992 ++ [F26] = L996 from rfl] at h
  rw [i464 hinj, i462 hinj, i463 hinj, i461 hinj] at h
  linarith

theorem row203 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L295 + (1 : ℝ) * HLm Γ 5 L999 + (-1 : ℝ) * HLm Γ 5 L1001 + (-1 : ℝ) * HLm Γ 5 L55 := by
  have h := HLm_submod hΓ [F0] L55 [F3]
  rw [show [F0] ++ L55 ++ [F3] = L1002 from rfl, show [F0] ++ L55 = L295 from rfl,
    show L55 ++ [F3] = L1000 from rfl] at h
  rw [i466 hinj, i465 hinj] at h
  linarith

theorem row204 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1003 + (1 : ℝ) * HLm Γ 5 L1005 + (-1 : ℝ) * HLm Γ 5 L1007 + (-1 : ℝ) * HLm Γ 5 L1009 := by
  have h := HLm_submod hΓ [F0] L1010 [F66]
  rw [show [F0] ++ L1010 ++ [F66] = L1008 from rfl, show [F0] ++ L1010 = L1004 from rfl,
    show L1010 ++ [F66] = L1006 from rfl] at h
  rw [i469 hinj, i467 hinj, i468 hinj, i470 hinj] at h
  linarith

theorem row205 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1011 + (1 : ℝ) * HLm Γ 5 L1013 + (-1 : ℝ) * HLm Γ 5 L1015 + (-1 : ℝ) * HLm Γ 5 L1009 := by
  have h := HLm_submod hΓ [F2] L1010 [F68]
  rw [show [F2] ++ L1010 ++ [F68] = L1016 from rfl, show [F2] ++ L1010 = L1012 from rfl,
    show L1010 ++ [F68] = L1014 from rfl] at h
  rw [i473 hinj, i471 hinj, i472 hinj, i470 hinj] at h
  linarith

theorem row206 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1017 + (1 : ℝ) * HLm Γ 5 L245 + (-1 : ℝ) * HLm Γ 5 L1020 + (-1 : ℝ) * HLm Γ 5 L243 := by
  have h := HLm_submod hΓ [F2] L244 [F67]
  rw [show [F2] ++ L244 ++ [F67] = L1021 from rfl, show [F2] ++ L244 = L1018 from rfl,
    show L244 ++ [F67] = L1019 from rfl] at h
  rw [i476 hinj, i474 hinj, i475 hinj, i88 hinj] at h
  linarith

theorem row207 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1022 + (1 : ℝ) * HLm Γ 5 L519 + (-1 : ℝ) * HLm Γ 5 L1025 + (-1 : ℝ) * HLm Γ 5 L247 := by
  have h := HLm_submod hΓ [F62] L371 [F23]
  rw [show [F62] ++ L371 ++ [F23] = L1026 from rfl, show [F62] ++ L371 = L1023 from rfl,
    show L371 ++ [F23] = L1024 from rfl] at h
  rw [i479 hinj, i477 hinj, i478 hinj, i148 hinj] at h
  linarith

theorem row208 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1027 + (1 : ℝ) * HLm Γ 5 L1029 + (-1 : ℝ) * HLm Γ 5 L1031 + (-1 : ℝ) * HLm Γ 5 L247 := by
  have h := HLm_submod hΓ [F3] L371 [F68]
  rw [show [F3] ++ L371 ++ [F68] = L1032 from rfl, show [F3] ++ L371 = L1028 from rfl,
    show L371 ++ [F68] = L1030 from rfl] at h
  rw [i482 hinj, i480 hinj, i481 hinj, i148 hinj] at h
  linarith

theorem row209 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1033 + (1 : ℝ) * HLm Γ 5 L1035 + (-1 : ℝ) * HLm Γ 5 L1037 + (-1 : ℝ) * HLm Γ 5 L1039 := by
  have h := HLm_submod hΓ [F7] L1040 [F3]
  rw [show [F7] ++ L1040 ++ [F3] = L1038 from rfl, show [F7] ++ L1040 = L1034 from rfl,
    show L1040 ++ [F3] = L1036 from rfl] at h
  rw [i485 hinj, i483 hinj, i484 hinj, i486 hinj] at h
  linarith

theorem row210 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1041 + (1 : ℝ) * HLm Γ 5 L250 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L248 := by
  have h := HLm_submod hΓ [F67] L249 [F30]
  rw [show [F67] ++ L249 ++ [F30] = L1045 from rfl, show [F67] ++ L249 = L1042 from rfl,
    show L249 ++ [F30] = L1043 from rfl] at h
  rw [i489 hinj, i487 hinj, i488 hinj, i90 hinj] at h
  linarith

theorem row211 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1047 + (1 : ℝ) * HLm Γ 5 L372 + (-1 : ℝ) * HLm Γ 5 L1050 + (-1 : ℝ) * HLm Γ 5 L497 := by
  have h := HLm_submod hΓ [F1] L1052 [F67]
  rw [show [F1] ++ L1052 ++ [F67] = L1051 from rfl, show [F1] ++ L1052 = L1048 from rfl,
    show L1052 ++ [F67] = L1049 from rfl] at h
  rw [i492 hinj, i490 hinj, i491 hinj, i493 hinj] at h
  linarith

theorem row212 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1053 + (1 : ℝ) * HLm Γ 5 L1055 + (-1 : ℝ) * HLm Γ 5 L1057 + (-1 : ℝ) * HLm Γ 5 L1059 := by
  have h := HLm_submod hΓ [F23] L1060 [F31]
  rw [show [F23] ++ L1060 ++ [F31] = L1058 from rfl, show [F23] ++ L1060 = L1054 from rfl,
    show L1060 ++ [F31] = L1056 from rfl] at h
  rw [i496 hinj, i494 hinj, i495 hinj, i497 hinj] at h
  linarith

theorem row213 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1061 + (1 : ℝ) * HLm Γ 5 L220 + (-1 : ℝ) * HLm Γ 5 L1064 + (-1 : ℝ) * HLm Γ 5 L273 := by
  have h := HLm_submod hΓ [F3] L273 [F16]
  rw [show [F3] ++ L273 ++ [F16] = L1065 from rfl, show [F3] ++ L273 = L1062 from rfl,
    show L273 ++ [F16] = L1063 from rfl] at h
  rw [i500 hinj, i498 hinj, i499 hinj] at h
  linarith

theorem row214 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1066 + (1 : ℝ) * HLm Γ 5 L286 + (-1 : ℝ) * HLm Γ 5 L1069 + (-1 : ℝ) * HLm Γ 5 L267 := by
  have h := HLm_submod hΓ [F0] L268 [F16]
  rw [show [F0] ++ L268 ++ [F16] = L1070 from rfl, show [F0] ++ L268 = L1067 from rfl,
    show L268 ++ [F16] = L1068 from rfl] at h
  rw [i503 hinj, i501 hinj, i502 hinj, i100 hinj] at h
  linarith

theorem row215 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L115 + (1 : ℝ) * HLm Γ 5 L269 + (-1 : ℝ) * HLm Γ 5 L900 + (-1 : ℝ) * HLm Γ 5 L254 := by
  have h := HLm_submod hΓ [F7] L255 [F2]
  rw [show [F7] ++ L255 ++ [F2] = L1073 from rfl, show [F7] ++ L255 = L1071 from rfl,
    show L255 ++ [F2] = L1072 from rfl] at h
  rw [i506 hinj, i504 hinj, i505 hinj, i93 hinj] at h
  linarith

theorem row216 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1074 + (1 : ℝ) * HLm Γ 5 L454 + (-1 : ℝ) * HLm Γ 5 L1077 + (-1 : ℝ) * HLm Γ 5 L452 := by
  have h := HLm_submod hΓ [F1] L452 [F16]
  rw [show [F1] ++ L452 ++ [F16] = L1078 from rfl, show [F1] ++ L452 = L1075 from rfl,
    show L452 ++ [F16] = L1076 from rfl] at h
  rw [i509 hinj, i507 hinj, i508 hinj] at h
  linarith

theorem row217 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1079 + (1 : ℝ) * HLm Γ 5 L1081 + (-1 : ℝ) * HLm Γ 5 L1083 + (-1 : ℝ) * HLm Γ 5 L1085 := by
  have h := HLm_submod hΓ [F1] L1086 [F16]
  rw [show [F1] ++ L1086 ++ [F16] = L1084 from rfl, show [F1] ++ L1086 = L1080 from rfl,
    show L1086 ++ [F16] = L1082 from rfl] at h
  rw [i512 hinj, i510 hinj, i511 hinj, i513 hinj] at h
  linarith

theorem row218 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1087 + (1 : ℝ) * HLm Γ 5 L1081 + (-1 : ℝ) * HLm Γ 5 L1089 + (-1 : ℝ) * HLm Γ 5 L1085 := by
  have h := HLm_submod hΓ [F47] L1086 [F16]
  rw [show [F47] ++ L1086 ++ [F16] = L1090 from rfl, show [F47] ++ L1086 = L1088 from rfl,
    show L1086 ++ [F16] = L1082 from rfl] at h
  rw [i515 hinj, i514 hinj, i511 hinj, i513 hinj] at h
  linarith

theorem row219 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L291 + (1 : ℝ) * HLm Γ 5 L1091 + (-1 : ℝ) * HLm Γ 5 L1093 + (-1 : ℝ) * HLm Γ 5 L289 := by
  have h := HLm_submod hΓ [F0] L290 [F5]
  rw [show [F0] ++ L290 ++ [F5] = L1094 from rfl, show [F0] ++ L290 = L292 from rfl,
    show L290 ++ [F5] = L1092 from rfl] at h
  rw [i517 hinj, i111 hinj, i516 hinj, i110 hinj] at h
  linarith

theorem row220 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1095 + (1 : ℝ) * HLm Γ 5 L1097 + (-1 : ℝ) * HLm Γ 5 L1099 + (-1 : ℝ) * HLm Γ 5 L323 := by
  have h := HLm_submod hΓ [F67] L1101 [F78]
  rw [show [F67] ++ L1101 ++ [F78] = L1100 from rfl, show [F67] ++ L1101 = L1096 from rfl,
    show L1101 ++ [F78] = L1098 from rfl] at h
  rw [i520 hinj, i518 hinj, i519 hinj, i521 hinj] at h
  linarith

theorem row221 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1102 + (1 : ℝ) * HLm Γ 5 L808 + (-1 : ℝ) * HLm Γ 5 L1105 + (-1 : ℝ) * HLm Γ 5 L299 := by
  have h := HLm_submod hΓ [F2] L300 [F9]
  rw [show [F2] ++ L300 ++ [F9] = L1106 from rfl, show [F2] ++ L300 = L1103 from rfl,
    show L300 ++ [F9] = L1104 from rfl] at h
  rw [i524 hinj, i522 hinj, i523 hinj, i115 hinj] at h
  linarith

theorem row222 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1107 + (1 : ℝ) * HLm Γ 5 L1109 + (-1 : ℝ) * HLm Γ 5 L1111 + (-1 : ℝ) * HLm Γ 5 L1113 := by
  have h := HLm_submod hΓ [F2] L1114 [F68]
  rw [show [F2] ++ L1114 ++ [F68] = L1112 from rfl, show [F2] ++ L1114 = L1108 from rfl,
    show L1114 ++ [F68] = L1110 from rfl] at h
  rw [i527 hinj, i525 hinj, i526 hinj, i528 hinj] at h
  linarith

theorem row223 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1115 + (1 : ℝ) * HLm Γ 5 L1117 + (-1 : ℝ) * HLm Γ 5 L1119 + (-1 : ℝ) * HLm Γ 5 L362 := by
  have h := HLm_submod hΓ [F2] L363 [F105]
  rw [show [F2] ++ L363 ++ [F105] = L1120 from rfl, show [F2] ++ L363 = L1116 from rfl,
    show L363 ++ [F105] = L1118 from rfl] at h
  rw [i531 hinj, i529 hinj, i530 hinj, i144 hinj] at h
  linarith

theorem row224 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L364 + (1 : ℝ) * HLm Γ 5 L1029 + (-1 : ℝ) * HLm Γ 5 L1031 + (-1 : ℝ) * HLm Γ 5 L362 := by
  have h := HLm_submod hΓ [F3] L363 [F22]
  rw [show [F3] ++ L363 ++ [F22] = L1122 from rfl, show [F3] ++ L363 = L365 from rfl,
    show L363 ++ [F22] = L1121 from rfl] at h
  rw [i533 hinj, i145 hinj, i532 hinj, i144 hinj] at h
  linarith

theorem row225 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1123 + (1 : ℝ) * HLm Γ 5 L1125 + (-1 : ℝ) * HLm Γ 5 L1127 + (-1 : ℝ) * HLm Γ 5 L356 := by
  have h := HLm_submod hΓ [F1] L357 [F9]
  rw [show [F1] ++ L357 ++ [F9] = L1128 from rfl, show [F1] ++ L357 = L1124 from rfl,
    show L357 ++ [F9] = L1126 from rfl] at h
  rw [i536 hinj, i534 hinj, i535 hinj, i141 hinj] at h
  linarith

theorem row226 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1129 + (1 : ℝ) * HLm Γ 5 L1131 + (-1 : ℝ) * HLm Γ 5 L1133 + (-1 : ℝ) * HLm Γ 5 L356 := by
  have h := HLm_submod hΓ [F12] L357 [F105]
  rw [show [F12] ++ L357 ++ [F105] = L1134 from rfl, show [F12] ++ L357 = L1130 from rfl,
    show L357 ++ [F105] = L1132 from rfl] at h
  rw [i539 hinj, i537 hinj, i538 hinj, i141 hinj] at h
  linarith

theorem row227 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1135 + (1 : ℝ) * HLm Γ 5 L376 + (-1 : ℝ) * HLm Γ 5 L1050 + (-1 : ℝ) * HLm Γ 5 L374 := by
  have h := HLm_submod hΓ [F1] L375 [F22]
  rw [show [F1] ++ L375 ++ [F22] = L1138 from rfl, show [F1] ++ L375 = L1136 from rfl,
    show L375 ++ [F22] = L1137 from rfl] at h
  rw [i542 hinj, i540 hinj, i541 hinj, i150 hinj] at h
  linarith

theorem row228 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L352 + (1 : ℝ) * HLm Γ 5 L380 + (-1 : ℝ) * HLm Γ 5 L1141 + (-1 : ℝ) * HLm Γ 5 L341 := by
  have h := HLm_submod hΓ [F2] L341 [F67]
  rw [show [F2] ++ L341 ++ [F67] = L1142 from rfl, show [F2] ++ L341 = L1139 from rfl,
    show L341 ++ [F67] = L1140 from rfl] at h
  rw [i545 hinj, i543 hinj, i544 hinj] at h
  linarith

theorem row229 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1143 + (1 : ℝ) * HLm Γ 5 L1145 + (-1 : ℝ) * HLm Γ 5 L1146 + (-1 : ℝ) * HLm Γ 5 L346 := by
  have h := HLm_submod hΓ [F7] L346 [F3]
  rw [show [F7] ++ L346 ++ [F3] = L1147 from rfl, show [F7] ++ L346 = L1144 from rfl,
    show L346 ++ [F3] = L1145 from rfl] at h
  rw [i547 hinj, i546 hinj] at h
  linarith

theorem row230 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1143 + (1 : ℝ) * HLm Γ 5 L1148 + (-1 : ℝ) * HLm Γ 5 L1150 + (-1 : ℝ) * HLm Γ 5 L346 := by
  have h := HLm_submod hΓ [F7] L346 [F55]
  rw [show [F7] ++ L346 ++ [F55] = L1151 from rfl, show [F7] ++ L346 = L1144 from rfl,
    show L346 ++ [F55] = L1149 from rfl] at h
  rw [i549 hinj, i546 hinj, i548 hinj] at h
  linarith

theorem row231 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1152 + (1 : ℝ) * HLm Γ 5 L358 + (-1 : ℝ) * HLm Γ 5 L1155 + (-1 : ℝ) * HLm Γ 5 L351 := by
  have h := HLm_submod hΓ [F12] L351 [F62]
  rw [show [F12] ++ L351 ++ [F62] = L1156 from rfl, show [F12] ++ L351 = L1153 from rfl,
    show L351 ++ [F62] = L1154 from rfl] at h
  rw [i552 hinj, i550 hinj, i551 hinj] at h
  linarith

theorem row232 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1157 + (1 : ℝ) * HLm Γ 5 L1159 + (-1 : ℝ) * HLm Γ 5 L1161 + (-1 : ℝ) * HLm Γ 5 L379 := by
  have h := HLm_submod hΓ [F7] L379 [F38]
  rw [show [F7] ++ L379 ++ [F38] = L1162 from rfl, show [F7] ++ L379 = L1158 from rfl,
    show L379 ++ [F38] = L1160 from rfl] at h
  rw [i555 hinj, i553 hinj, i554 hinj] at h
  linarith

theorem row233 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1163 + (1 : ℝ) * HLm Γ 5 L218 + (-1 : ℝ) * HLm Γ 5 L847 + (-1 : ℝ) * HLm Γ 5 L1167 := by
  have h := HLm_submod hΓ [F12] L1168 [F44]
  rw [show [F12] ++ L1168 ++ [F44] = L1166 from rfl, show [F12] ++ L1168 = L1164 from rfl,
    show L1168 ++ [F44] = L1165 from rfl] at h
  rw [i558 hinj, i556 hinj, i557 hinj, i559 hinj] at h
  linarith

theorem row234 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1135 + (1 : ℝ) * HLm Γ 5 L536 + (-1 : ℝ) * HLm Γ 5 L1171 + (-1 : ℝ) * HLm Γ 5 L1173 := by
  have h := HLm_submod hΓ [F1] L1174 [F7]
  rw [show [F1] ++ L1174 ++ [F7] = L1172 from rfl, show [F1] ++ L1174 = L1169 from rfl,
    show L1174 ++ [F7] = L1170 from rfl] at h
  rw [i562 hinj, i560 hinj, i561 hinj, i563 hinj] at h
  linarith

theorem row235 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1175 + (1 : ℝ) * HLm Γ 5 L408 + (-1 : ℝ) * HLm Γ 5 L1178 + (-1 : ℝ) * HLm Γ 5 L406 := by
  have h := HLm_submod hΓ [F3] L407 [F17]
  rw [show [F3] ++ L407 ++ [F17] = L1179 from rfl, show [F3] ++ L407 = L1176 from rfl,
    show L407 ++ [F17] = L1177 from rfl] at h
  rw [i566 hinj, i564 hinj, i565 hinj, i164 hinj] at h
  linarith

theorem row236 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L396 + (1 : ℝ) * HLm Γ 5 L1180 + (-1 : ℝ) * HLm Γ 5 L1182 + (-1 : ℝ) * HLm Γ 5 L394 := by
  have h := HLm_submod hΓ [F0] L395 [F62]
  rw [show [F0] ++ L395 ++ [F62] = L1183 from rfl, show [F0] ++ L395 = L397 from rfl,
    show L395 ++ [F62] = L1181 from rfl] at h
  rw [i568 hinj, i159 hinj, i567 hinj, i158 hinj] at h
  linarith

theorem row237 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1180 + (1 : ℝ) * HLm Γ 5 L1185 + (-1 : ℝ) * HLm Γ 5 L1187 + (-1 : ℝ) * HLm Γ 5 L545 := by
  have h := HLm_submod hΓ [F62] L1189 [F3]
  rw [show [F62] ++ L1189 ++ [F3] = L1188 from rfl, show [F62] ++ L1189 = L1184 from rfl,
    show L1189 ++ [F3] = L1186 from rfl] at h
  rw [i571 hinj, i569 hinj, i570 hinj, i572 hinj] at h
  linarith

theorem row238 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1190 + (1 : ℝ) * HLm Γ 5 L413 + (-1 : ℝ) * HLm Γ 5 L1193 + (-1 : ℝ) * HLm Γ 5 L411 := by
  have h := HLm_submod hΓ [F1] L412 [F38]
  rw [show [F1] ++ L412 ++ [F38] = L1194 from rfl, show [F1] ++ L412 = L1191 from rfl,
    show L412 ++ [F38] = L1192 from rfl] at h
  rw [i575 hinj, i573 hinj, i574 hinj, i167 hinj] at h
  linarith

theorem row239 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L358 + (1 : ℝ) * HLm Γ 5 L1196 + (-1 : ℝ) * HLm Γ 5 L1198 + (-1 : ℝ) * HLm Γ 5 L1200 := by
  have h := HLm_submod hΓ [F62] L1201 [F3]
  rw [show [F62] ++ L1201 ++ [F3] = L1199 from rfl, show [F62] ++ L1201 = L1195 from rfl,
    show L1201 ++ [F3] = L1197 from rfl] at h
  rw [i578 hinj, i576 hinj, i577 hinj, i579 hinj] at h
  linarith

theorem row240 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1202 + (1 : ℝ) * HLm Γ 5 L325 + (-1 : ℝ) * HLm Γ 5 L1205 + (-1 : ℝ) * HLm Γ 5 L1207 := by
  have h := HLm_submod hΓ [F1] L1208 [F27]
  rw [show [F1] ++ L1208 ++ [F27] = L1206 from rfl, show [F1] ++ L1208 = L1203 from rfl,
    show L1208 ++ [F27] = L1204 from rfl] at h
  rw [i582 hinj, i580 hinj, i581 hinj, i583 hinj] at h
  linarith

theorem row241 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1209 + (1 : ℝ) * HLm Γ 5 L1211 + (-1 : ℝ) * HLm Γ 5 L1213 + (-1 : ℝ) * HLm Γ 5 L431 := by
  have h := HLm_submod hΓ [F3] L432 [F68]
  rw [show [F3] ++ L432 ++ [F68] = L1214 from rfl, show [F3] ++ L432 = L1210 from rfl,
    show L432 ++ [F68] = L1212 from rfl] at h
  rw [i586 hinj, i584 hinj, i585 hinj, i176 hinj] at h
  linarith

theorem row242 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1215 + (1 : ℝ) * HLm Γ 5 L1217 + (-1 : ℝ) * HLm Γ 5 L1219 + (-1 : ℝ) * HLm Γ 5 L1221 := by
  have h := HLm_submod hΓ [F7] L1222 [F2]
  rw [show [F7] ++ L1222 ++ [F2] = L1220 from rfl, show [F7] ++ L1222 = L1216 from rfl,
    show L1222 ++ [F2] = L1218 from rfl] at h
  rw [i589 hinj, i587 hinj, i588 hinj, i590 hinj] at h
  linarith

theorem row243 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1223 + (1 : ℝ) * HLm Γ 5 L1225 + (-1 : ℝ) * HLm Γ 5 L1227 + (-1 : ℝ) * HLm Γ 5 L528 := by
  have h := HLm_submod hΓ [F7] L1229 [F2]
  rw [show [F7] ++ L1229 ++ [F2] = L1228 from rfl, show [F7] ++ L1229 = L1224 from rfl,
    show L1229 ++ [F2] = L1226 from rfl] at h
  rw [i593 hinj, i591 hinj, i592 hinj, i594 hinj] at h
  linarith

theorem row244 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1230 + (1 : ℝ) * HLm Γ 5 L1232 + (-1 : ℝ) * HLm Γ 5 L1234 + (-1 : ℝ) * HLm Γ 5 L1236 := by
  have h := HLm_submod hΓ [F62] L1237 [F33]
  rw [show [F62] ++ L1237 ++ [F33] = L1235 from rfl, show [F62] ++ L1237 = L1231 from rfl,
    show L1237 ++ [F33] = L1233 from rfl] at h
  rw [i597 hinj, i595 hinj, i596 hinj, i598 hinj] at h
  linarith

theorem row245 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L851 + (1 : ℝ) * HLm Γ 5 L1239 + (-1 : ℝ) * HLm Γ 5 L1241 + (-1 : ℝ) * HLm Γ 5 L555 := by
  have h := HLm_submod hΓ [F7] L1243 [F48]
  rw [show [F7] ++ L1243 ++ [F48] = L1242 from rfl, show [F7] ++ L1243 = L1238 from rfl,
    show L1243 ++ [F48] = L1240 from rfl] at h
  rw [i601 hinj, i599 hinj, i600 hinj, i602 hinj] at h
  linarith

theorem row246 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L851 + (1 : ℝ) * HLm Γ 5 L1245 + (-1 : ℝ) * HLm Γ 5 L842 + (-1 : ℝ) * HLm Γ 5 L565 := by
  have h := HLm_submod hΓ [F7] L1248 [F45]
  rw [show [F7] ++ L1248 ++ [F45] = L1247 from rfl, show [F7] ++ L1248 = L1244 from rfl,
    show L1248 ++ [F45] = L1246 from rfl] at h
  rw [i605 hinj, i603 hinj, i604 hinj, i606 hinj] at h
  linarith

theorem row247 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L558 + (1 : ℝ) * HLm Γ 5 L745 + (-1 : ℝ) * HLm Γ 5 L1251 + (-1 : ℝ) * HLm Γ 5 L741 := by
  have h := HLm_submod hΓ [F44] L1253 [F67]
  rw [show [F44] ++ L1253 ++ [F67] = L1252 from rfl, show [F44] ++ L1253 = L1249 from rfl,
    show L1253 ++ [F67] = L1250 from rfl] at h
  rw [i609 hinj, i607 hinj, i608 hinj, i610 hinj] at h
  linarith

theorem row248 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L260 + (1 : ℝ) * HLm Γ 5 L1255 + (-1 : ℝ) * HLm Γ 5 L1257 + (-1 : ℝ) * HLm Γ 5 L1003 := by
  have h := HLm_submod hΓ [F1] L1259 [F23]
  rw [show [F1] ++ L1259 ++ [F23] = L1258 from rfl, show [F1] ++ L1259 = L1254 from rfl,
    show L1259 ++ [F23] = L1256 from rfl] at h
  rw [i613 hinj, i611 hinj, i612 hinj, i614 hinj] at h
  linarith

theorem row249 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1260 + (1 : ℝ) * HLm Γ 5 L1262 + (-1 : ℝ) * HLm Γ 5 L1264 + (-1 : ℝ) * HLm Γ 5 L1266 := by
  have h := HLm_submod hΓ [F2] L1267 [F68]
  rw [show [F2] ++ L1267 ++ [F68] = L1265 from rfl, show [F2] ++ L1267 = L1261 from rfl,
    show L1267 ++ [F68] = L1263 from rfl] at h
  rw [i617 hinj, i615 hinj, i616 hinj, i618 hinj] at h
  linarith

theorem row250 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L683 + (1 : ℝ) * HLm Γ 5 L858 + (-1 : ℝ) * HLm Γ 5 L842 + (-1 : ℝ) * HLm Γ 5 L256 := by
  have h := HLm_submod hΓ [F1] L1271 [F2]
  rw [show [F1] ++ L1271 ++ [F2] = L1270 from rfl, show [F1] ++ L1271 = L1268 from rfl,
    show L1271 ++ [F2] = L1269 from rfl] at h
  rw [i621 hinj, i619 hinj, i620 hinj, i622 hinj] at h
  linarith

theorem row251 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L851 + (1 : ℝ) * HLm Γ 5 L563 + (-1 : ℝ) * HLm Γ 5 L1241 + (-1 : ℝ) * HLm Γ 5 L560 := by
  have h := HLm_submod hΓ [F1] L1275 [F48]
  rw [show [F1] ++ L1275 ++ [F48] = L1274 from rfl, show [F1] ++ L1275 = L1272 from rfl,
    show L1275 ++ [F48] = L1273 from rfl] at h
  rw [i625 hinj, i623 hinj, i624 hinj, i626 hinj] at h
  linarith

theorem row252 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1276 + (1 : ℝ) * HLm Γ 5 L597 + (-1 : ℝ) * HLm Γ 5 L1278 + (-1 : ℝ) * HLm Γ 5 L1280 := by
  have h := HLm_submod hΓ [F1] L1280 [F67]
  rw [show [F1] ++ L1280 ++ [F67] = L1279 from rfl, show [F1] ++ L1280 = L1277 from rfl,
    show L1280 ++ [F67] = L597 from rfl] at h
  rw [i628 hinj, i627 hinj] at h
  linarith

theorem row253 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1281 + (1 : ℝ) * HLm Γ 5 L1283 + (-1 : ℝ) * HLm Γ 5 L1285 + (-1 : ℝ) * HLm Γ 5 L580 := by
  have h := HLm_submod hΓ [F16] L1287 [F23]
  rw [show [F16] ++ L1287 ++ [F23] = L1286 from rfl, show [F16] ++ L1287 = L1282 from rfl,
    show L1287 ++ [F23] = L1284 from rfl] at h
  rw [i631 hinj, i629 hinj, i630 hinj, i632 hinj] at h
  linarith

theorem row254 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L599 + (1 : ℝ) * HLm Γ 5 L583 + (-1 : ℝ) * HLm Γ 5 L1290 + (-1 : ℝ) * HLm Γ 5 L562 := by
  have h := HLm_submod hΓ [F16] L562 [F25]
  rw [show [F16] ++ L562 ++ [F25] = L1291 from rfl, show [F16] ++ L562 = L1288 from rfl,
    show L562 ++ [F25] = L1289 from rfl] at h
  rw [i635 hinj, i633 hinj, i634 hinj] at h
  linarith

theorem row255 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1292 + (1 : ℝ) * HLm Γ 5 L1294 + (-1 : ℝ) * HLm Γ 5 L1295 + (-1 : ℝ) * HLm Γ 5 L1297 := by
  have h := HLm_submod hΓ [F62] L1297 [F67]
  rw [show [F62] ++ L1297 ++ [F67] = L1296 from rfl, show [F62] ++ L1297 = L1293 from rfl,
    show L1297 ++ [F67] = L1294 from rfl] at h
  rw [i637 hinj, i636 hinj] at h
  linarith

theorem row256 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1298 + (1 : ℝ) * HLm Γ 5 L989 + (-1 : ℝ) * HLm Γ 5 L1301 + (-1 : ℝ) * HLm Γ 5 L1303 := by
  have h := HLm_submod hΓ [F1] L1304 [F68]
  rw [show [F1] ++ L1304 ++ [F68] = L1302 from rfl, show [F1] ++ L1304 = L1299 from rfl,
    show L1304 ++ [F68] = L1300 from rfl] at h
  rw [i640 hinj, i638 hinj, i639 hinj, i641 hinj] at h
  linarith

theorem row257 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1305 + (1 : ℝ) * HLm Γ 5 L989 + (-1 : ℝ) * HLm Γ 5 L1307 + (-1 : ℝ) * HLm Γ 5 L1303 := by
  have h := HLm_submod hΓ [F62] L1304 [F68]
  rw [show [F62] ++ L1304 ++ [F68] = L1308 from rfl, show [F62] ++ L1304 = L1306 from rfl,
    show L1304 ++ [F68] = L1300 from rfl] at h
  rw [i643 hinj, i642 hinj, i639 hinj, i641 hinj] at h
  linarith

theorem row258 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1309 + (1 : ℝ) * HLm Γ 5 L1311 + (-1 : ℝ) * HLm Γ 5 L1313 + (-1 : ℝ) * HLm Γ 5 L1315 := by
  have h := HLm_submod hΓ [F67] L1316 [F86]
  rw [show [F67] ++ L1316 ++ [F86] = L1314 from rfl, show [F67] ++ L1316 = L1310 from rfl,
    show L1316 ++ [F86] = L1312 from rfl] at h
  rw [i646 hinj, i644 hinj, i645 hinj, i647 hinj] at h
  linarith

theorem row259 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1317 + (1 : ℝ) * HLm Γ 5 L1319 + (-1 : ℝ) * HLm Γ 5 L1321 + (-1 : ℝ) * HLm Γ 5 L567 := by
  have h := HLm_submod hΓ [F16] L567 [F50]
  rw [show [F16] ++ L567 ++ [F50] = L1322 from rfl, show [F16] ++ L567 = L1318 from rfl,
    show L567 ++ [F50] = L1320 from rfl] at h
  rw [i650 hinj, i648 hinj, i649 hinj] at h
  linarith

theorem row260 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1323 + (1 : ℝ) * HLm Γ 5 L1325 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L1328 := by
  have h := HLm_submod hΓ [F7] L1329 [F23]
  rw [show [F7] ++ L1329 ++ [F23] = L1327 from rfl, show [F7] ++ L1329 = L1324 from rfl,
    show L1329 ++ [F23] = L1326 from rfl] at h
  rw [i653 hinj, i651 hinj, i652 hinj, i654 hinj] at h
  linarith

theorem row261 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1330 + (1 : ℝ) * HLm Γ 5 L1332 + (-1 : ℝ) * HLm Γ 5 L1334 + (-1 : ℝ) * HLm Γ 5 L1336 := by
  have h := HLm_submod hΓ [F7] L1337 [F3]
  rw [show [F7] ++ L1337 ++ [F3] = L1335 from rfl, show [F7] ++ L1337 = L1331 from rfl,
    show L1337 ++ [F3] = L1333 from rfl] at h
  rw [i657 hinj, i655 hinj, i656 hinj, i658 hinj] at h
  linarith

theorem row262 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L845 + (1 : ℝ) * HLm Γ 5 L1339 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L986 := by
  have h := HLm_submod hΓ [F7] L987 [F25]
  rw [show [F7] ++ L987 ++ [F25] = L1341 from rfl, show [F7] ++ L987 = L1338 from rfl,
    show L987 ++ [F25] = L1340 from rfl] at h
  rw [i661 hinj, i659 hinj, i660 hinj, i458 hinj] at h
  linarith

theorem row263 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1323 + (1 : ℝ) * HLm Γ 5 L604 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L1345 := by
  have h := HLm_submod hΓ [F7] L1346 [F23]
  rw [show [F7] ++ L1346 ++ [F23] = L1344 from rfl, show [F7] ++ L1346 = L1342 from rfl,
    show L1346 ++ [F23] = L1343 from rfl] at h
  rw [i664 hinj, i662 hinj, i663 hinj, i665 hinj] at h
  linarith

theorem row264 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L568 + (1 : ℝ) * HLm Γ 5 L1348 + (-1 : ℝ) * HLm Γ 5 L1350 + (-1 : ℝ) * HLm Γ 5 L582 := by
  have h := HLm_submod hΓ [F1] L582 [F16]
  rw [show [F1] ++ L582 ++ [F16] = L1351 from rfl, show [F1] ++ L582 = L1347 from rfl,
    show L582 ++ [F16] = L1349 from rfl] at h
  rw [i668 hinj, i666 hinj, i667 hinj] at h
  linarith

theorem row265 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L851 + (1 : ℝ) * HLm Γ 5 L1227 + (-1 : ℝ) * HLm Γ 5 L842 + (-1 : ℝ) * HLm Γ 5 L707 := by
  have h := HLm_submod hΓ [F0] L1355 [F45]
  rw [show [F0] ++ L1355 ++ [F45] = L1354 from rfl, show [F0] ++ L1355 = L1352 from rfl,
    show L1355 ++ [F45] = L1353 from rfl] at h
  rw [i671 hinj, i669 hinj, i670 hinj, i672 hinj] at h
  linarith

theorem row266 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L851 + (1 : ℝ) * HLm Γ 5 L900 + (-1 : ℝ) * HLm Γ 5 L842 + (-1 : ℝ) * HLm Γ 5 L897 := by
  have h := HLm_submod hΓ [F0] L1359 [F45]
  rw [show [F0] ++ L1359 ++ [F45] = L1358 from rfl, show [F0] ++ L1359 = L1356 from rfl,
    show L1359 ++ [F45] = L1357 from rfl] at h
  rw [i675 hinj, i673 hinj, i674 hinj, i676 hinj] at h
  linarith

theorem row267 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L851 + (1 : ℝ) * HLm Γ 5 L1360 + (-1 : ℝ) * HLm Γ 5 L1241 + (-1 : ℝ) * HLm Γ 5 L897 := by
  have h := HLm_submod hΓ [F0] L1359 [F48]
  rw [show [F0] ++ L1359 ++ [F48] = L1362 from rfl, show [F0] ++ L1359 = L1356 from rfl,
    show L1359 ++ [F48] = L1361 from rfl] at h
  rw [i678 hinj, i673 hinj, i677 hinj, i676 hinj] at h
  linarith

theorem row268 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1363 + (1 : ℝ) * HLm Γ 5 L1365 + (-1 : ℝ) * HLm Γ 5 L1367 + (-1 : ℝ) * HLm Γ 5 L1369 := by
  have h := HLm_submod hΓ [F1] L1370 [F38]
  rw [show [F1] ++ L1370 ++ [F38] = L1368 from rfl, show [F1] ++ L1370 = L1364 from rfl,
    show L1370 ++ [F38] = L1366 from rfl] at h
  rw [i681 hinj, i679 hinj, i680 hinj, i682 hinj] at h
  linarith

theorem row269 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L851 + (1 : ℝ) * HLm Γ 5 L1372 + (-1 : ℝ) * HLm Γ 5 L842 + (-1 : ℝ) * HLm Γ 5 L624 := by
  have h := HLm_submod hΓ [F0] L1375 [F45]
  rw [show [F0] ++ L1375 ++ [F45] = L1374 from rfl, show [F0] ++ L1375 = L1371 from rfl,
    show L1375 ++ [F45] = L1373 from rfl] at h
  rw [i685 hinj, i683 hinj, i684 hinj, i686 hinj] at h
  linarith

theorem row270 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1376 + (1 : ℝ) * HLm Γ 5 L1378 + (-1 : ℝ) * HLm Γ 5 L1380 + (-1 : ℝ) * HLm Γ 5 L1382 := by
  have h := HLm_submod hΓ [F2] L1383 [F82]
  rw [show [F2] ++ L1383 ++ [F82] = L1381 from rfl, show [F2] ++ L1383 = L1377 from rfl,
    show L1383 ++ [F82] = L1379 from rfl] at h
  rw [i689 hinj, i687 hinj, i688 hinj, i690 hinj] at h
  linarith

theorem row271 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L627 + (1 : ℝ) * HLm Γ 5 L1385 + (-1 : ℝ) * HLm Γ 5 L1387 + (-1 : ℝ) * HLm Γ 5 L1389 := by
  have h := HLm_submod hΓ [F111] L1390 [F16]
  rw [show [F111] ++ L1390 ++ [F16] = L1388 from rfl, show [F111] ++ L1390 = L1384 from rfl,
    show L1390 ++ [F16] = L1386 from rfl] at h
  rw [i693 hinj, i691 hinj, i692 hinj, i694 hinj] at h
  linarith

theorem row272 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L683 + (1 : ℝ) * HLm Γ 5 L1392 + (-1 : ℝ) * HLm Γ 5 L1257 + (-1 : ℝ) * HLm Γ 5 L1395 := by
  have h := HLm_submod hΓ [F0] L1396 [F16]
  rw [show [F0] ++ L1396 ++ [F16] = L1394 from rfl, show [F0] ++ L1396 = L1391 from rfl,
    show L1396 ++ [F16] = L1393 from rfl] at h
  rw [i697 hinj, i695 hinj, i696 hinj, i698 hinj] at h
  linarith

theorem row273 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L851 + (1 : ℝ) * HLm Γ 5 L1398 + (-1 : ℝ) * HLm Γ 5 L1241 + (-1 : ℝ) * HLm Γ 5 L1401 := by
  have h := HLm_submod hΓ [F0] L1402 [F48]
  rw [show [F0] ++ L1402 ++ [F48] = L1400 from rfl, show [F0] ++ L1402 = L1397 from rfl,
    show L1402 ++ [F48] = L1399 from rfl] at h
  rw [i701 hinj, i699 hinj, i700 hinj, i702 hinj] at h
  linarith

theorem row274 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L638 + (1 : ℝ) * HLm Γ 5 L1404 + (-1 : ℝ) * HLm Γ 5 L1406 + (-1 : ℝ) * HLm Γ 5 L1408 := by
  have h := HLm_submod hΓ [F0] L1409 [F87]
  rw [show [F0] ++ L1409 ++ [F87] = L1407 from rfl, show [F0] ++ L1409 = L1403 from rfl,
    show L1409 ++ [F87] = L1405 from rfl] at h
  rw [i705 hinj, i703 hinj, i704 hinj, i706 hinj] at h
  linarith

theorem row275 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1410 + (1 : ℝ) * HLm Γ 5 L1412 + (-1 : ℝ) * HLm Γ 5 L1414 + (-1 : ℝ) * HLm Γ 5 L1416 := by
  have h := HLm_submod hΓ [F67] L1417 [F86]
  rw [show [F67] ++ L1417 ++ [F86] = L1415 from rfl, show [F67] ++ L1417 = L1411 from rfl,
    show L1417 ++ [F86] = L1413 from rfl] at h
  rw [i709 hinj, i707 hinj, i708 hinj, i710 hinj] at h
  linarith

theorem row276 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L689 + (1 : ℝ) * HLm Γ 5 L1418 + (-1 : ℝ) * HLm Γ 5 L1420 + (-1 : ℝ) * HLm Γ 5 L626 := by
  have h := HLm_submod hΓ [F0] L626 [F16]
  rw [show [F0] ++ L626 ++ [F16] = L1421 from rfl, show [F0] ++ L626 = L689 from rfl,
    show L626 ++ [F16] = L1419 from rfl] at h
  rw [i712 hinj, i711 hinj] at h
  linarith

theorem row277 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L845 + (1 : ℝ) * HLm Γ 5 L1423 + (-1 : ℝ) * HLm Γ 5 L1420 + (-1 : ℝ) * HLm Γ 5 L673 := by
  have h := HLm_submod hΓ [F0] L1426 [F3]
  rw [show [F0] ++ L1426 ++ [F3] = L1425 from rfl, show [F0] ++ L1426 = L1422 from rfl,
    show L1426 ++ [F3] = L1424 from rfl] at h
  rw [i715 hinj, i713 hinj, i714 hinj, i716 hinj] at h
  linarith

theorem row278 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L845 + (1 : ℝ) * HLm Γ 5 L1428 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L1431 := by
  have h := HLm_submod hΓ [F0] L1432 [F4]
  rw [show [F0] ++ L1432 ++ [F4] = L1430 from rfl, show [F0] ++ L1432 = L1427 from rfl,
    show L1432 ++ [F4] = L1429 from rfl] at h
  rw [i719 hinj, i717 hinj, i718 hinj, i720 hinj] at h
  linarith

theorem row279 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1433 + (1 : ℝ) * HLm Γ 5 L633 + (-1 : ℝ) * HLm Γ 5 L1436 + (-1 : ℝ) * HLm Γ 5 L631 := by
  have h := HLm_submod hΓ [F1] L632 [F67]
  rw [show [F1] ++ L632 ++ [F67] = L1437 from rfl, show [F1] ++ L632 = L1434 from rfl,
    show L632 ++ [F67] = L1435 from rfl] at h
  rw [i723 hinj, i721 hinj, i722 hinj, i271 hinj] at h
  linarith

theorem row280 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1438 + (1 : ℝ) * HLm Γ 5 L1440 + (-1 : ℝ) * HLm Γ 5 L1442 + (-1 : ℝ) * HLm Γ 5 L1157 := by
  have h := HLm_submod hΓ [F2] L1444 [F82]
  rw [show [F2] ++ L1444 ++ [F82] = L1443 from rfl, show [F2] ++ L1444 = L1439 from rfl,
    show L1444 ++ [F82] = L1441 from rfl] at h
  rw [i726 hinj, i724 hinj, i725 hinj, i727 hinj] at h
  linarith

theorem row281 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1445 + (1 : ℝ) * HLm Γ 5 L1447 + (-1 : ℝ) * HLm Γ 5 L1449 + (-1 : ℝ) * HLm Γ 5 L1157 := by
  have h := HLm_submod hΓ [F111] L1444 [F67]
  rw [show [F111] ++ L1444 ++ [F67] = L1450 from rfl, show [F111] ++ L1444 = L1446 from rfl,
    show L1444 ++ [F67] = L1448 from rfl] at h
  rw [i730 hinj, i728 hinj, i729 hinj, i727 hinj] at h
  linarith

theorem row282 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L1453 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L1456 := by
  have h := HLm_submod hΓ [F0] L1457 [F67]
  rw [show [F0] ++ L1457 ++ [F67] = L1455 from rfl, show [F0] ++ L1457 = L1452 from rfl,
    show L1457 ++ [F67] = L1454 from rfl] at h
  rw [i733 hinj, i731 hinj, i732 hinj, i734 hinj] at h
  linarith

theorem row283 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1458 + (1 : ℝ) * HLm Γ 5 L666 + (-1 : ℝ) * HLm Γ 5 L1461 + (-1 : ℝ) * HLm Γ 5 L1463 := by
  have h := HLm_submod hΓ [F0] L1464 [F55]
  rw [show [F0] ++ L1464 ++ [F55] = L1462 from rfl, show [F0] ++ L1464 = L1459 from rfl,
    show L1464 ++ [F55] = L1460 from rfl] at h
  rw [i737 hinj, i735 hinj, i736 hinj, i738 hinj] at h
  linarith

theorem row284 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1465 + (1 : ℝ) * HLm Γ 5 L1467 + (-1 : ℝ) * HLm Γ 5 L1469 + (-1 : ℝ) * HLm Γ 5 L129 := by
  have h := HLm_submod hΓ [F1] L1471 [F9]
  rw [show [F1] ++ L1471 ++ [F9] = L1470 from rfl, show [F1] ++ L1471 = L1466 from rfl,
    show L1471 ++ [F9] = L1468 from rfl] at h
  rw [i741 hinj, i739 hinj, i740 hinj, i742 hinj] at h
  linarith

theorem row285 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L614 + (1 : ℝ) * HLm Γ 5 L1473 + (-1 : ℝ) * HLm Γ 5 L904 + (-1 : ℝ) * HLm Γ 5 L1102 := by
  have h := HLm_submod hΓ [F1] L1103 [F7]
  rw [show [F1] ++ L1103 ++ [F7] = L1475 from rfl, show [F1] ++ L1103 = L1472 from rfl,
    show L1103 ++ [F7] = L1474 from rfl] at h
  rw [i745 hinj, i743 hinj, i744 hinj, i522 hinj] at h
  linarith

theorem row286 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L851 + (1 : ℝ) * HLm Γ 5 L1477 + (-1 : ℝ) * HLm Γ 5 L1451 + (-1 : ℝ) * HLm Γ 5 L1480 := by
  have h := HLm_submod hΓ [F0] L1481 [F16]
  rw [show [F0] ++ L1481 ++ [F16] = L1479 from rfl, show [F0] ++ L1481 = L1476 from rfl,
    show L1481 ++ [F16] = L1478 from rfl] at h
  rw [i748 hinj, i746 hinj, i747 hinj, i749 hinj] at h
  linarith

theorem row287 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1482 + (1 : ℝ) * HLm Γ 5 L1484 + (-1 : ℝ) * HLm Γ 5 L1486 + (-1 : ℝ) * HLm Γ 5 L1488 := by
  have h := HLm_submod hΓ [F2] L1489 [F67]
  rw [show [F2] ++ L1489 ++ [F67] = L1487 from rfl, show [F2] ++ L1489 = L1483 from rfl,
    show L1489 ++ [F67] = L1485 from rfl] at h
  rw [i752 hinj, i750 hinj, i751 hinj, i753 hinj] at h
  linarith

theorem row288 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1490 + (1 : ℝ) * HLm Γ 5 L1492 + (-1 : ℝ) * HLm Γ 5 L1494 + (-1 : ℝ) * HLm Γ 5 L718 := by
  have h := HLm_submod hΓ [F7] L1496 [F52]
  rw [show [F7] ++ L1496 ++ [F52] = L1495 from rfl, show [F7] ++ L1496 = L1491 from rfl,
    show L1496 ++ [F52] = L1493 from rfl] at h
  rw [i756 hinj, i754 hinj, i755 hinj, i757 hinj] at h
  linarith

theorem row289 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L710 + (1 : ℝ) * HLm Γ 5 L728 + (-1 : ℝ) * HLm Γ 5 L1498 + (-1 : ℝ) * HLm Γ 5 L709 := by
  have h := HLm_submod hΓ [F7] L709 [F16]
  rw [show [F7] ++ L709 ++ [F16] = L1499 from rfl, show [F7] ++ L709 = L711 from rfl,
    show L709 ++ [F16] = L1497 from rfl] at h
  rw [i759 hinj, i311 hinj, i758 hinj] at h
  linarith

theorem row290 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1500 + (1 : ℝ) * HLm Γ 5 L1502 + (-1 : ℝ) * HLm Γ 5 L1504 + (-1 : ℝ) * HLm Γ 5 L1506 := by
  have h := HLm_submod hΓ [F16] L1507 [F117]
  rw [show [F16] ++ L1507 ++ [F117] = L1505 from rfl, show [F16] ++ L1507 = L1501 from rfl,
    show L1507 ++ [F117] = L1503 from rfl] at h
  rw [i762 hinj, i760 hinj, i761 hinj, i763 hinj] at h
  linarith

theorem row291 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L731 + (1 : ℝ) * HLm Γ 5 L1089 + (-1 : ℝ) * HLm Γ 5 L1509 + (-1 : ℝ) * HLm Γ 5 L1087 := by
  have h := HLm_submod hΓ [F0] L1088 [F16]
  rw [show [F0] ++ L1088 ++ [F16] = L1510 from rfl, show [F0] ++ L1088 = L1508 from rfl,
    show L1088 ++ [F16] = L1090 from rfl] at h
  rw [i765 hinj, i764 hinj, i515 hinj, i514 hinj] at h
  linarith

theorem row292 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L863 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L860 := by
  have h := HLm_submod hΓ [F51] L861 [F67]
  rw [show [F51] ++ L861 ++ [F67] = L1512 from rfl, show [F51] ++ L861 = L1511 from rfl,
    show L861 ++ [F67] = L864 from rfl] at h
  rw [i767 hinj, i766 hinj, i393 hinj, i392 hinj] at h
  linarith

theorem row293 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1513 + (1 : ℝ) * HLm Γ 5 L1515 + (-1 : ℝ) * HLm Γ 5 L1517 + (-1 : ℝ) * HLm Γ 5 L770 := by
  have h := HLm_submod hΓ [F16] L1519 [F117]
  rw [show [F16] ++ L1519 ++ [F117] = L1518 from rfl, show [F16] ++ L1519 = L1514 from rfl,
    show L1519 ++ [F117] = L1516 from rfl] at h
  rw [i770 hinj, i768 hinj, i769 hinj, i771 hinj] at h
  linarith

theorem row294 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1520 + (1 : ℝ) * HLm Γ 5 L1522 + (-1 : ℝ) * HLm Γ 5 L1524 + (-1 : ℝ) * HLm Γ 5 L1526 := by
  have h := HLm_submod hΓ [F0] L1527 [F20]
  rw [show [F0] ++ L1527 ++ [F20] = L1525 from rfl, show [F0] ++ L1527 = L1521 from rfl,
    show L1527 ++ [F20] = L1523 from rfl] at h
  rw [i774 hinj, i772 hinj, i773 hinj, i775 hinj] at h
  linarith

theorem row295 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1528 + (1 : ℝ) * HLm Γ 5 L1530 + (-1 : ℝ) * HLm Γ 5 L1532 + (-1 : ℝ) * HLm Γ 5 L1534 := by
  have h := HLm_submod hΓ [F67] L1535 [F17]
  rw [show [F67] ++ L1535 ++ [F17] = L1533 from rfl, show [F67] ++ L1535 = L1529 from rfl,
    show L1535 ++ [F17] = L1531 from rfl] at h
  rw [i778 hinj, i776 hinj, i777 hinj, i779 hinj] at h
  linarith

theorem row296 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L845 + (1 : ℝ) * HLm Γ 5 L1537 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L808 := by
  have h := HLm_submod hΓ [F0] L1540 [F4]
  rw [show [F0] ++ L1540 ++ [F4] = L1539 from rfl, show [F0] ++ L1540 = L1536 from rfl,
    show L1540 ++ [F4] = L1538 from rfl] at h
  rw [i782 hinj, i780 hinj, i781 hinj, i783 hinj] at h
  linarith

theorem row297 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L845 + (1 : ℝ) * HLm Γ 5 L1542 + (-1 : ℝ) * HLm Γ 5 L1420 + (-1 : ℝ) * HLm Γ 5 L1545 := by
  have h := HLm_submod hΓ [F0] L1546 [F3]
  rw [show [F0] ++ L1546 ++ [F3] = L1544 from rfl, show [F0] ++ L1546 = L1541 from rfl,
    show L1546 ++ [F3] = L1543 from rfl] at h
  rw [i786 hinj, i784 hinj, i785 hinj, i787 hinj] at h
  linarith

theorem row298 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L845 + (1 : ℝ) * HLm Γ 5 L761 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L757 := by
  have h := HLm_submod hΓ [F0] L1550 [F25]
  rw [show [F0] ++ L1550 ++ [F25] = L1549 from rfl, show [F0] ++ L1550 = L1547 from rfl,
    show L1550 ++ [F25] = L1548 from rfl] at h
  rw [i790 hinj, i788 hinj, i789 hinj, i791 hinj] at h
  linarith

theorem row299 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1551 + (1 : ℝ) * HLm Γ 5 L1553 + (-1 : ℝ) * HLm Γ 5 L1555 + (-1 : ℝ) * HLm Γ 5 L759 := by
  have h := HLm_submod hΓ [F51] L760 [F67]
  rw [show [F51] ++ L760 ++ [F67] = L1556 from rfl, show [F51] ++ L760 = L1552 from rfl,
    show L760 ++ [F67] = L1554 from rfl] at h
  rw [i794 hinj, i792 hinj, i793 hinj, i335 hinj] at h
  linarith

end EntropyBounds.TwoSet.Certs.R7A5
