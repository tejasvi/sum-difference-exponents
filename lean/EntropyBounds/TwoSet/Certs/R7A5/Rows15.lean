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

theorem row2250 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L10200 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10197 := by
  have h := HLm_submod hΓ [F0] L10913 [F210]
  rw [show [F0] ++ L10913 ++ [F210] = L10912 from rfl, show [F0] ++ L10913 = L10910 from rfl,
    show L10913 ++ [F210] = L10911 from rfl] at h
  rw [i6641 hinj, i6639 hinj, i6640 hinj, i6642 hinj] at h
  linarith

theorem row2251 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L10194 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10182 := by
  have h := HLm_submod hΓ [F0] L10917 [F210]
  rw [show [F0] ++ L10917 ++ [F210] = L10916 from rfl, show [F0] ++ L10917 = L10914 from rfl,
    show L10917 ++ [F210] = L10915 from rfl] at h
  rw [i6645 hinj, i6643 hinj, i6644 hinj, i6646 hinj] at h
  linarith

theorem row2252 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4558 + (1 : ℝ) * HLm Γ 5 L10919 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10922 := by
  have h := HLm_submod hΓ [F0] L10923 [F67]
  rw [show [F0] ++ L10923 ++ [F67] = L10921 from rfl, show [F0] ++ L10923 = L10918 from rfl,
    show L10923 ++ [F67] = L10920 from rfl] at h
  rw [i6649 hinj, i6647 hinj, i6648 hinj, i6650 hinj] at h
  linarith

theorem row2253 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L10178 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10176 := by
  have h := HLm_submod hΓ [F0] L10927 [F210]
  rw [show [F0] ++ L10927 ++ [F210] = L10926 from rfl, show [F0] ++ L10927 = L10924 from rfl,
    show L10927 ++ [F210] = L10925 from rfl] at h
  rw [i6653 hinj, i6651 hinj, i6652 hinj, i6654 hinj] at h
  linarith

theorem row2254 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L10631 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10628 := by
  have h := HLm_submod hΓ [F0] L10629 [F210]
  rw [show [F0] ++ L10629 ++ [F210] = L10929 from rfl, show [F0] ++ L10629 = L10928 from rfl,
    show L10629 ++ [F210] = L10632 from rfl] at h
  rw [i6656 hinj, i6655 hinj, i6388 hinj, i6386 hinj] at h
  linarith

theorem row2255 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L10217 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10215 := by
  have h := HLm_submod hΓ [F0] L10933 [F210]
  rw [show [F0] ++ L10933 ++ [F210] = L10932 from rfl, show [F0] ++ L10933 = L10930 from rfl,
    show L10933 ++ [F210] = L10931 from rfl] at h
  rw [i6659 hinj, i6657 hinj, i6658 hinj, i6660 hinj] at h
  linarith

theorem row2256 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4558 + (1 : ℝ) * HLm Γ 5 L10234 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10227 := by
  have h := HLm_submod hΓ [F0] L10228 [F67]
  rw [show [F0] ++ L10228 ++ [F67] = L10935 from rfl, show [F0] ++ L10228 = L10229 from rfl,
    show L10228 ++ [F67] = L10934 from rfl] at h
  rw [i6662 hinj, i6116 hinj, i6661 hinj, i6115 hinj] at h
  linarith

theorem row2257 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L10249 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10246 := by
  have h := HLm_submod hΓ [F0] L10939 [F210]
  rw [show [F0] ++ L10939 ++ [F210] = L10938 from rfl, show [F0] ++ L10939 = L10936 from rfl,
    show L10939 ++ [F210] = L10937 from rfl] at h
  rw [i6665 hinj, i6663 hinj, i6664 hinj, i6666 hinj] at h
  linarith

theorem row2258 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L10293 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10290 := by
  have h := HLm_submod hΓ [F0] L10943 [F210]
  rw [show [F0] ++ L10943 ++ [F210] = L10942 from rfl, show [F0] ++ L10943 = L10940 from rfl,
    show L10943 ++ [F210] = L10941 from rfl] at h
  rw [i6669 hinj, i6667 hinj, i6668 hinj, i6670 hinj] at h
  linarith

theorem row2259 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L10266 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10260 := by
  have h := HLm_submod hΓ [F0] L10947 [F210]
  rw [show [F0] ++ L10947 ++ [F210] = L10946 from rfl, show [F0] ++ L10947 = L10944 from rfl,
    show L10947 ++ [F210] = L10945 from rfl] at h
  rw [i6673 hinj, i6671 hinj, i6672 hinj, i6674 hinj] at h
  linarith

theorem row2260 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L10256 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10254 := by
  have h := HLm_submod hΓ [F0] L10255 [F210]
  rw [show [F0] ++ L10255 ++ [F210] = L10950 from rfl, show [F0] ++ L10255 = L10948 from rfl,
    show L10255 ++ [F210] = L10949 from rfl] at h
  rw [i6677 hinj, i6675 hinj, i6676 hinj, i6135 hinj] at h
  linarith

theorem row2261 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L10280 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10278 := by
  have h := HLm_submod hΓ [F0] L10954 [F210]
  rw [show [F0] ++ L10954 ++ [F210] = L10953 from rfl, show [F0] ++ L10954 = L10951 from rfl,
    show L10954 ++ [F210] = L10952 from rfl] at h
  rw [i6680 hinj, i6678 hinj, i6679 hinj, i6681 hinj] at h
  linarith

theorem row2262 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L10286 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10284 := by
  have h := HLm_submod hΓ [F0] L10285 [F210]
  rw [show [F0] ++ L10285 ++ [F210] = L10957 from rfl, show [F0] ++ L10285 = L10955 from rfl,
    show L10285 ++ [F210] = L10956 from rfl] at h
  rw [i6684 hinj, i6682 hinj, i6683 hinj, i6155 hinj] at h
  linarith

theorem row2263 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L10959 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10962 := by
  have h := HLm_submod hΓ [F0] L10963 [F210]
  rw [show [F0] ++ L10963 ++ [F210] = L10961 from rfl, show [F0] ++ L10963 = L10958 from rfl,
    show L10963 ++ [F210] = L10960 from rfl] at h
  rw [i6687 hinj, i6685 hinj, i6686 hinj, i6688 hinj] at h
  linarith

theorem row2264 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10964 + (1 : ℝ) * HLm Γ 5 L5515 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10312 := by
  have h := HLm_submod hΓ [F1] L10968 [F0]
  rw [show [F1] ++ L10968 ++ [F0] = L10967 from rfl, show [F1] ++ L10968 = L10965 from rfl,
    show L10968 ++ [F0] = L10966 from rfl] at h
  rw [i6691 hinj, i6689 hinj, i6690 hinj, i6692 hinj] at h
  linarith

theorem row2265 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10969 + (1 : ℝ) * HLm Γ 5 L5515 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10336 := by
  have h := HLm_submod hΓ [F1] L10973 [F0]
  rw [show [F1] ++ L10973 ++ [F0] = L10972 from rfl, show [F1] ++ L10973 = L10970 from rfl,
    show L10973 ++ [F0] = L10971 from rfl] at h
  rw [i6695 hinj, i6693 hinj, i6694 hinj, i6696 hinj] at h
  linarith

theorem row2266 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5925 + (1 : ℝ) * HLm Γ 5 L6462 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10327 := by
  have h := HLm_submod hΓ [F1] L10977 [F0]
  rw [show [F1] ++ L10977 ++ [F0] = L10976 from rfl, show [F1] ++ L10977 = L10974 from rfl,
    show L10977 ++ [F0] = L10975 from rfl] at h
  rw [i6699 hinj, i6697 hinj, i6698 hinj, i6700 hinj] at h
  linarith

theorem row2267 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L10333 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10331 := by
  have h := HLm_submod hΓ [F0] L10332 [F210]
  rw [show [F0] ++ L10332 ++ [F210] = L10980 from rfl, show [F0] ++ L10332 = L10978 from rfl,
    show L10332 ++ [F210] = L10979 from rfl] at h
  rw [i6703 hinj, i6701 hinj, i6702 hinj, i6187 hinj] at h
  linarith

theorem row2268 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L10611 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10609 := by
  have h := HLm_submod hΓ [F0] L10610 [F210]
  rw [show [F0] ++ L10610 ++ [F210] = L10982 from rfl, show [F0] ++ L10610 = L10981 from rfl,
    show L10610 ++ [F210] = L10612 from rfl] at h
  rw [i6705 hinj, i6704 hinj, i6372 hinj, i6371 hinj] at h
  linarith

theorem row2269 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L10362 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10360 := by
  have h := HLm_submod hΓ [F0] L10986 [F210]
  rw [show [F0] ++ L10986 ++ [F210] = L10985 from rfl, show [F0] ++ L10986 = L10983 from rfl,
    show L10986 ++ [F210] = L10984 from rfl] at h
  rw [i6708 hinj, i6706 hinj, i6707 hinj, i6709 hinj] at h
  linarith

theorem row2270 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6089 + (1 : ℝ) * HLm Γ 5 L10375 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10373 := by
  have h := HLm_submod hΓ [F1] L10990 [F0]
  rw [show [F1] ++ L10990 ++ [F0] = L10989 from rfl, show [F1] ++ L10990 = L10987 from rfl,
    show L10990 ++ [F0] = L10988 from rfl] at h
  rw [i6712 hinj, i6710 hinj, i6711 hinj, i6713 hinj] at h
  linarith

theorem row2271 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5925 + (1 : ℝ) * HLm Γ 5 L5814 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10379 := by
  have h := HLm_submod hΓ [F1] L10994 [F0]
  rw [show [F1] ++ L10994 ++ [F0] = L10993 from rfl, show [F1] ++ L10994 = L10991 from rfl,
    show L10994 ++ [F0] = L10992 from rfl] at h
  rw [i6716 hinj, i6714 hinj, i6715 hinj, i6717 hinj] at h
  linarith

theorem row2272 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6089 + (1 : ℝ) * HLm Γ 5 L10393 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10391 := by
  have h := HLm_submod hΓ [F1] L10998 [F0]
  rw [show [F1] ++ L10998 ++ [F0] = L10997 from rfl, show [F1] ++ L10998 = L10995 from rfl,
    show L10998 ++ [F0] = L10996 from rfl] at h
  rw [i6720 hinj, i6718 hinj, i6719 hinj, i6721 hinj] at h
  linarith

theorem row2273 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4932 + (1 : ℝ) * HLm Γ 5 L6179 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L4919 := by
  have h := HLm_submod hΓ [F1] L6178 [F0]
  rw [show [F1] ++ L6178 ++ [F0] = L11001 from rfl, show [F1] ++ L6178 = L10999 from rfl,
    show L6178 ++ [F0] = L11000 from rfl] at h
  rw [i6724 hinj, i6722 hinj, i6723 hinj, i3546 hinj] at h
  linarith

theorem row2274 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L10409 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10405 := by
  have h := HLm_submod hΓ [F0] L11005 [F210]
  rw [show [F0] ++ L11005 ++ [F210] = L11004 from rfl, show [F0] ++ L11005 = L11002 from rfl,
    show L11005 ++ [F210] = L11003 from rfl] at h
  rw [i6727 hinj, i6725 hinj, i6726 hinj, i6728 hinj] at h
  linarith

theorem row2275 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L10402 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10400 := by
  have h := HLm_submod hΓ [F0] L10401 [F210]
  rw [show [F0] ++ L10401 ++ [F210] = L11008 from rfl, show [F0] ++ L10401 = L11006 from rfl,
    show L10401 ++ [F210] = L11007 from rfl] at h
  rw [i6731 hinj, i6729 hinj, i6730 hinj, i6235 hinj] at h
  linarith

theorem row2276 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6396 + (1 : ℝ) * HLm Γ 5 L10417 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10415 := by
  have h := HLm_submod hΓ [F0] L10416 [F7]
  rw [show [F0] ++ L10416 ++ [F7] = L11011 from rfl, show [F0] ++ L10416 = L11009 from rfl,
    show L10416 ++ [F7] = L11010 from rfl] at h
  rw [i6734 hinj, i6732 hinj, i6733 hinj, i6243 hinj] at h
  linarith

theorem row2277 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L10425 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10423 := by
  have h := HLm_submod hΓ [F0] L11015 [F210]
  rw [show [F0] ++ L11015 ++ [F210] = L11014 from rfl, show [F0] ++ L11015 = L11012 from rfl,
    show L11015 ++ [F210] = L11013 from rfl] at h
  rw [i6737 hinj, i6735 hinj, i6736 hinj, i6738 hinj] at h
  linarith

theorem row2278 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4558 + (1 : ℝ) * HLm Γ 5 L10437 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10435 := by
  have h := HLm_submod hΓ [F0] L11019 [F67]
  rw [show [F0] ++ L11019 ++ [F67] = L11018 from rfl, show [F0] ++ L11019 = L11016 from rfl,
    show L11019 ++ [F67] = L11017 from rfl] at h
  rw [i6741 hinj, i6739 hinj, i6740 hinj, i6742 hinj] at h
  linarith

theorem row2279 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L10454 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L9057 := by
  have h := HLm_submod hΓ [F0] L11023 [F210]
  rw [show [F0] ++ L11023 ++ [F210] = L11022 from rfl, show [F0] ++ L11023 = L11020 from rfl,
    show L11023 ++ [F210] = L11021 from rfl] at h
  rw [i6745 hinj, i6743 hinj, i6744 hinj, i6746 hinj] at h
  linarith

theorem row2280 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L10460 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10458 := by
  have h := HLm_submod hΓ [F0] L11027 [F210]
  rw [show [F0] ++ L11027 ++ [F210] = L11026 from rfl, show [F0] ++ L11027 = L11024 from rfl,
    show L11027 ++ [F210] = L11025 from rfl] at h
  rw [i6749 hinj, i6747 hinj, i6748 hinj, i6750 hinj] at h
  linarith

theorem row2281 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L10650 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10647 := by
  have h := HLm_submod hΓ [F0] L10648 [F210]
  rw [show [F0] ++ L10648 ++ [F210] = L11029 from rfl, show [F0] ++ L10648 = L11028 from rfl,
    show L10648 ++ [F210] = L10651 from rfl] at h
  rw [i6752 hinj, i6751 hinj, i6404 hinj, i6402 hinj] at h
  linarith

theorem row2282 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L10587 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10584 := by
  have h := HLm_submod hΓ [F0] L10585 [F210]
  rw [show [F0] ++ L10585 ++ [F210] = L11031 from rfl, show [F0] ++ L10585 = L11030 from rfl,
    show L10585 ++ [F210] = L10588 from rfl] at h
  rw [i6754 hinj, i6753 hinj, i6356 hinj, i6354 hinj] at h
  linarith

theorem row2283 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L10471 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10469 := by
  have h := HLm_submod hΓ [F0] L11035 [F210]
  rw [show [F0] ++ L11035 ++ [F210] = L11034 from rfl, show [F0] ++ L11035 = L11032 from rfl,
    show L11035 ++ [F210] = L11033 from rfl] at h
  rw [i6757 hinj, i6755 hinj, i6756 hinj, i6758 hinj] at h
  linarith

theorem row2284 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11036 + (1 : ℝ) * HLm Γ 5 L11038 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L11041 := by
  have h := HLm_submod hΓ [F0] L11042 [F7]
  rw [show [F0] ++ L11042 ++ [F7] = L11040 from rfl, show [F0] ++ L11042 = L11037 from rfl,
    show L11042 ++ [F7] = L11039 from rfl] at h
  rw [i6761 hinj, i6759 hinj, i6760 hinj, i6762 hinj] at h
  linarith

theorem row2285 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L10592 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10589 := by
  have h := HLm_submod hΓ [F0] L10590 [F210]
  rw [show [F0] ++ L10590 ++ [F210] = L11044 from rfl, show [F0] ++ L10590 = L11043 from rfl,
    show L10590 ++ [F210] = L10593 from rfl] at h
  rw [i6764 hinj, i6763 hinj, i6359 hinj, i6357 hinj] at h
  linarith

theorem row2286 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6270 + (1 : ℝ) * HLm Γ 5 L6782 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L6262 := by
  have h := HLm_submod hΓ [F0] L6263 [F7]
  rw [show [F0] ++ L6263 ++ [F7] = L11046 from rfl, show [F0] ++ L6263 = L6755 from rfl,
    show L6263 ++ [F7] = L11045 from rfl] at h
  rw [i6766 hinj, i4015 hinj, i6765 hinj, i3608 hinj] at h
  linarith

theorem row2287 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L10516 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10514 := by
  have h := HLm_submod hΓ [F0] L11050 [F210]
  rw [show [F0] ++ L11050 ++ [F210] = L11049 from rfl, show [F0] ++ L11050 = L11047 from rfl,
    show L11050 ++ [F210] = L11048 from rfl] at h
  rw [i6769 hinj, i6767 hinj, i6768 hinj, i6770 hinj] at h
  linarith

theorem row2288 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11051 + (1 : ℝ) * HLm Γ 5 L6782 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10522 := by
  have h := HLm_submod hΓ [F0] L10523 [F7]
  rw [show [F0] ++ L10523 ++ [F7] = L11054 from rfl, show [F0] ++ L10523 = L11052 from rfl,
    show L10523 ++ [F7] = L11053 from rfl] at h
  rw [i6773 hinj, i6771 hinj, i6772 hinj, i6314 hinj] at h
  linarith

theorem row2289 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L10553 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10551 := by
  have h := HLm_submod hΓ [F0] L11058 [F210]
  rw [show [F0] ++ L11058 ++ [F210] = L11057 from rfl, show [F0] ++ L11058 = L11055 from rfl,
    show L11058 ++ [F210] = L11056 from rfl] at h
  rw [i6776 hinj, i6774 hinj, i6775 hinj, i6777 hinj] at h
  linarith

theorem row2290 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11059 + (1 : ℝ) * HLm Γ 5 L10537 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10533 := by
  have h := HLm_submod hΓ [F7] L11063 [F33]
  rw [show [F7] ++ L11063 ++ [F33] = L11062 from rfl, show [F7] ++ L11063 = L11060 from rfl,
    show L11063 ++ [F33] = L11061 from rfl] at h
  rw [i6780 hinj, i6778 hinj, i6779 hinj, i6781 hinj] at h
  linarith

theorem row2291 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L6788 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10535 := by
  have h := HLm_submod hΓ [F0] L11067 [F228]
  rw [show [F0] ++ L11067 ++ [F228] = L11066 from rfl, show [F0] ++ L11067 = L11064 from rfl,
    show L11067 ++ [F228] = L11065 from rfl] at h
  rw [i6784 hinj, i6782 hinj, i6783 hinj, i6785 hinj] at h
  linarith

theorem row2292 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L10549 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10547 := by
  have h := HLm_submod hΓ [F0] L11071 [F210]
  rw [show [F0] ++ L11071 ++ [F210] = L11070 from rfl, show [F0] ++ L11071 = L11068 from rfl,
    show L11071 ++ [F210] = L11069 from rfl] at h
  rw [i6788 hinj, i6786 hinj, i6787 hinj, i6789 hinj] at h
  linarith

theorem row2293 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L10576 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10574 := by
  have h := HLm_submod hΓ [F0] L11075 [F210]
  rw [show [F0] ++ L11075 ++ [F210] = L11074 from rfl, show [F0] ++ L11075 = L11072 from rfl,
    show L11075 ++ [F210] = L11073 from rfl] at h
  rw [i6792 hinj, i6790 hinj, i6791 hinj, i6793 hinj] at h
  linarith

theorem row2294 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L10580 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10578 := by
  have h := HLm_submod hΓ [F0] L11079 [F210]
  rw [show [F0] ++ L11079 ++ [F210] = L11078 from rfl, show [F0] ++ L11079 = L11076 from rfl,
    show L11079 ++ [F210] = L11077 from rfl] at h
  rw [i6796 hinj, i6794 hinj, i6795 hinj, i6797 hinj] at h
  linarith

theorem row2295 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10659 + (1 : ℝ) * HLm Γ 5 L6785 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10657 := by
  have h := HLm_submod hΓ [F7] L10658 [F111]
  rw [show [F7] ++ L10658 ++ [F111] = L11081 from rfl, show [F7] ++ L10658 = L10660 from rfl,
    show L10658 ++ [F111] = L11080 from rfl] at h
  rw [i6799 hinj, i6410 hinj, i6798 hinj, i6409 hinj] at h
  linarith

theorem row2296 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11082 + (1 : ℝ) * HLm Γ 5 L11084 + (-1 : ℝ) * HLm Γ 5 L11086 + (-1 : ℝ) * HLm Γ 5 L11088 := by
  have h := HLm_submod hΓ [F107] L11088 [F5]
  rw [show [F107] ++ L11088 ++ [F5] = L11087 from rfl, show [F107] ++ L11088 = L11083 from rfl,
    show L11088 ++ [F5] = L11085 from rfl] at h
  rw [i6802 hinj, i6800 hinj, i6801 hinj] at h
  linarith

theorem row2297 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11089 + (1 : ℝ) * HLm Γ 5 L11091 + (-1 : ℝ) * HLm Γ 5 L9765 + (-1 : ℝ) * HLm Γ 5 L11094 := by
  have h := HLm_submod hΓ [F0] L11095 [F7]
  rw [show [F0] ++ L11095 ++ [F7] = L11093 from rfl, show [F0] ++ L11095 = L11090 from rfl,
    show L11095 ++ [F7] = L11092 from rfl] at h
  rw [i6805 hinj, i6803 hinj, i6804 hinj, i6806 hinj] at h
  linarith

theorem row2298 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11096 + (1 : ℝ) * HLm Γ 5 L5188 + (-1 : ℝ) * HLm Γ 5 L11099 + (-1 : ℝ) * HLm Γ 5 L11101 := by
  have h := HLm_submod hΓ [F12] L11102 [F46]
  rw [show [F12] ++ L11102 ++ [F46] = L11100 from rfl, show [F12] ++ L11102 = L11097 from rfl,
    show L11102 ++ [F46] = L11098 from rfl] at h
  rw [i6809 hinj, i6807 hinj, i6808 hinj, i6810 hinj] at h
  linarith

theorem row2299 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11103 + (1 : ℝ) * HLm Γ 5 L11105 + (-1 : ℝ) * HLm Γ 5 L5668 + (-1 : ℝ) * HLm Γ 5 L3279 := by
  have h := HLm_submod hΓ [F1] L7965 [F5]
  rw [show [F1] ++ L7965 ++ [F5] = L11107 from rfl, show [F1] ++ L7965 = L11104 from rfl,
    show L7965 ++ [F5] = L11106 from rfl] at h
  rw [i6813 hinj, i6811 hinj, i6812 hinj, i4696 hinj] at h
  linarith

theorem row2300 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11108 + (1 : ℝ) * HLm Γ 5 L11110 + (-1 : ℝ) * HLm Γ 5 L5489 + (-1 : ℝ) * HLm Γ 5 L11113 := by
  have h := HLm_submod hΓ [F2] L11114 [F46]
  rw [show [F2] ++ L11114 ++ [F46] = L11112 from rfl, show [F2] ++ L11114 = L11109 from rfl,
    show L11114 ++ [F46] = L11111 from rfl] at h
  rw [i6816 hinj, i6814 hinj, i6815 hinj, i6817 hinj] at h
  linarith

theorem row2301 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11115 + (1 : ℝ) * HLm Γ 5 L11117 + (-1 : ℝ) * HLm Γ 5 L10063 + (-1 : ℝ) * HLm Γ 5 L11120 := by
  have h := HLm_submod hΓ [F2] L11121 [F67]
  rw [show [F2] ++ L11121 ++ [F67] = L11119 from rfl, show [F2] ++ L11121 = L11116 from rfl,
    show L11121 ++ [F67] = L11118 from rfl] at h
  rw [i6820 hinj, i6818 hinj, i6819 hinj, i6821 hinj] at h
  linarith

theorem row2302 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11122 + (1 : ℝ) * HLm Γ 5 L11124 + (-1 : ℝ) * HLm Γ 5 L11126 + (-1 : ℝ) * HLm Γ 5 L11128 := by
  have h := HLm_submod hΓ [F1] L11129 [F12]
  rw [show [F1] ++ L11129 ++ [F12] = L11127 from rfl, show [F1] ++ L11129 = L11123 from rfl,
    show L11129 ++ [F12] = L11125 from rfl] at h
  rw [i6824 hinj, i6822 hinj, i6823 hinj, i6825 hinj] at h
  linarith

theorem row2303 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11130 + (1 : ℝ) * HLm Γ 5 L11132 + (-1 : ℝ) * HLm Γ 5 L11134 + (-1 : ℝ) * HLm Γ 5 L351 := by
  have h := HLm_submod hΓ [F210] L351 [F117]
  rw [show [F210] ++ L351 ++ [F117] = L11135 from rfl, show [F210] ++ L351 = L11131 from rfl,
    show L351 ++ [F117] = L11133 from rfl] at h
  rw [i6828 hinj, i6826 hinj, i6827 hinj] at h
  linarith

theorem row2304 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11136 + (1 : ℝ) * HLm Γ 5 L11138 + (-1 : ℝ) * HLm Γ 5 L11140 + (-1 : ℝ) * HLm Γ 5 L11142 := by
  have h := HLm_submod hΓ [F0] L11143 [F7]
  rw [show [F0] ++ L11143 ++ [F7] = L11141 from rfl, show [F0] ++ L11143 = L11137 from rfl,
    show L11143 ++ [F7] = L11139 from rfl] at h
  rw [i6831 hinj, i6829 hinj, i6830 hinj, i6832 hinj] at h
  linarith

theorem row2305 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9202 + (1 : ℝ) * HLm Γ 5 L11145 + (-1 : ℝ) * HLm Γ 5 L4252 + (-1 : ℝ) * HLm Γ 5 L11148 := by
  have h := HLm_submod hΓ [F0] L11149 [F4]
  rw [show [F0] ++ L11149 ++ [F4] = L11147 from rfl, show [F0] ++ L11149 = L11144 from rfl,
    show L11149 ++ [F4] = L11146 from rfl] at h
  rw [i6835 hinj, i6833 hinj, i6834 hinj, i6836 hinj] at h
  linarith

theorem row2306 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9555 + (1 : ℝ) * HLm Γ 5 L11151 + (-1 : ℝ) * HLm Γ 5 L11153 + (-1 : ℝ) * HLm Γ 5 L11155 := by
  have h := HLm_submod hΓ [F1] L11156 [F7]
  rw [show [F1] ++ L11156 ++ [F7] = L11154 from rfl, show [F1] ++ L11156 = L11150 from rfl,
    show L11156 ++ [F7] = L11152 from rfl] at h
  rw [i6839 hinj, i6837 hinj, i6838 hinj, i6840 hinj] at h
  linarith

theorem row2307 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11157 + (1 : ℝ) * HLm Γ 5 L7155 + (-1 : ℝ) * HLm Γ 5 L11160 + (-1 : ℝ) * HLm Γ 5 L7154 := by
  have h := HLm_submod hΓ [F67] L7154 [F25]
  rw [show [F67] ++ L7154 ++ [F25] = L11161 from rfl, show [F67] ++ L7154 = L11158 from rfl,
    show L7154 ++ [F25] = L11159 from rfl] at h
  rw [i6843 hinj, i6841 hinj, i6842 hinj] at h
  linarith

theorem row2308 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11162 + (1 : ℝ) * HLm Γ 5 L11164 + (-1 : ℝ) * HLm Γ 5 L11166 + (-1 : ℝ) * HLm Γ 5 L11168 := by
  have h := HLm_submod hΓ [F9] L11169 [F82]
  rw [show [F9] ++ L11169 ++ [F82] = L11167 from rfl, show [F9] ++ L11169 = L11163 from rfl,
    show L11169 ++ [F82] = L11165 from rfl] at h
  rw [i6846 hinj, i6844 hinj, i6845 hinj, i6847 hinj] at h
  linarith

theorem row2309 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1698 + (1 : ℝ) * HLm Γ 5 L11171 + (-1 : ℝ) * HLm Γ 5 L11091 + (-1 : ℝ) * HLm Γ 5 L11174 := by
  have h := HLm_submod hΓ [F21] L11175 [F210]
  rw [show [F21] ++ L11175 ++ [F210] = L11173 from rfl, show [F21] ++ L11175 = L11170 from rfl,
    show L11175 ++ [F210] = L11172 from rfl] at h
  rw [i6850 hinj, i6848 hinj, i6849 hinj, i6851 hinj] at h
  linarith

theorem row2310 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11176 + (1 : ℝ) * HLm Γ 5 L11178 + (-1 : ℝ) * HLm Γ 5 L11180 + (-1 : ℝ) * HLm Γ 5 L11182 := by
  have h := HLm_submod hΓ [F9] L11183 [F3]
  rw [show [F9] ++ L11183 ++ [F3] = L11181 from rfl, show [F9] ++ L11183 = L11177 from rfl,
    show L11183 ++ [F3] = L11179 from rfl] at h
  rw [i6854 hinj, i6852 hinj, i6853 hinj, i6855 hinj] at h
  linarith

theorem row2311 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3279 + (1 : ℝ) * HLm Γ 5 L11185 + (-1 : ℝ) * HLm Γ 5 L4429 + (-1 : ℝ) * HLm Γ 5 L3277 := by
  have h := HLm_submod hΓ [F7] L11188 [F16]
  rw [show [F7] ++ L11188 ++ [F16] = L11187 from rfl, show [F7] ++ L11188 = L11184 from rfl,
    show L11188 ++ [F16] = L11186 from rfl] at h
  rw [i6858 hinj, i6856 hinj, i6857 hinj, i6859 hinj] at h
  linarith

theorem row2312 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11189 + (1 : ℝ) * HLm Γ 5 L11191 + (-1 : ℝ) * HLm Γ 5 L5889 + (-1 : ℝ) * HLm Γ 5 L11194 := by
  have h := HLm_submod hΓ [F2] L11195 [F15]
  rw [show [F2] ++ L11195 ++ [F15] = L11193 from rfl, show [F2] ++ L11195 = L11190 from rfl,
    show L11195 ++ [F15] = L11192 from rfl] at h
  rw [i6862 hinj, i6860 hinj, i6861 hinj, i6863 hinj] at h
  linarith

theorem row2313 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1363 + (1 : ℝ) * HLm Γ 5 L11197 + (-1 : ℝ) * HLm Γ 5 L5851 + (-1 : ℝ) * HLm Γ 5 L11200 := by
  have h := HLm_submod hΓ [F1] L11201 [F219]
  rw [show [F1] ++ L11201 ++ [F219] = L11199 from rfl, show [F1] ++ L11201 = L11196 from rfl,
    show L11201 ++ [F219] = L11198 from rfl] at h
  rw [i6866 hinj, i6864 hinj, i6865 hinj, i6867 hinj] at h
  linarith

theorem row2314 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11145 + (1 : ℝ) * HLm Γ 5 L5489 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L11205 := by
  have h := HLm_submod hΓ [F1] L11206 [F10]
  rw [show [F1] ++ L11206 ++ [F10] = L11204 from rfl, show [F1] ++ L11206 = L11202 from rfl,
    show L11206 ++ [F10] = L11203 from rfl] at h
  rw [i6870 hinj, i6868 hinj, i6869 hinj, i6871 hinj] at h
  linarith

theorem row2315 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5197 + (1 : ℝ) * HLm Γ 5 L11208 + (-1 : ℝ) * HLm Γ 5 L11210 + (-1 : ℝ) * HLm Γ 5 L11212 := by
  have h := HLm_submod hΓ [F16] L11213 [F40]
  rw [show [F16] ++ L11213 ++ [F40] = L11211 from rfl, show [F16] ++ L11213 = L11207 from rfl,
    show L11213 ++ [F40] = L11209 from rfl] at h
  rw [i6874 hinj, i6872 hinj, i6873 hinj, i6875 hinj] at h
  linarith

theorem row2316 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11214 + (1 : ℝ) * HLm Γ 5 L11086 + (-1 : ℝ) * HLm Γ 5 L11216 + (-1 : ℝ) * HLm Γ 5 L11082 := by
  have h := HLm_submod hΓ [F1] L11083 [F5]
  rw [show [F1] ++ L11083 ++ [F5] = L11217 from rfl, show [F1] ++ L11083 = L11215 from rfl,
    show L11083 ++ [F5] = L11087 from rfl] at h
  rw [i6877 hinj, i6876 hinj, i6802 hinj, i6800 hinj] at h
  linarith

theorem row2317 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11218 + (1 : ℝ) * HLm Γ 5 L11220 + (-1 : ℝ) * HLm Γ 5 L11221 + (-1 : ℝ) * HLm Γ 5 L11223 := by
  have h := HLm_submod hΓ [F1] L11223 [F214]
  rw [show [F1] ++ L11223 ++ [F214] = L11222 from rfl, show [F1] ++ L11223 = L11219 from rfl,
    show L11223 ++ [F214] = L11220 from rfl] at h
  rw [i6879 hinj, i6878 hinj] at h
  linarith

theorem row2318 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11224 + (1 : ℝ) * HLm Γ 5 L11226 + (-1 : ℝ) * HLm Γ 5 L11228 + (-1 : ℝ) * HLm Γ 5 L11230 := by
  have h := HLm_submod hΓ [F62] L11231 [F85]
  rw [show [F62] ++ L11231 ++ [F85] = L11229 from rfl, show [F62] ++ L11231 = L11225 from rfl,
    show L11231 ++ [F85] = L11227 from rfl] at h
  rw [i6882 hinj, i6880 hinj, i6881 hinj, i6883 hinj] at h
  linarith

theorem row2319 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11232 + (1 : ℝ) * HLm Γ 5 L11234 + (-1 : ℝ) * HLm Γ 5 L11235 + (-1 : ℝ) * HLm Γ 5 L11237 := by
  have h := HLm_submod hΓ [F210] L11237 [F15]
  rw [show [F210] ++ L11237 ++ [F15] = L11236 from rfl, show [F210] ++ L11237 = L11233 from rfl,
    show L11237 ++ [F15] = L11234 from rfl] at h
  rw [i6885 hinj, i6884 hinj] at h
  linarith

theorem row2320 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11238 + (1 : ℝ) * HLm Γ 5 L11240 + (-1 : ℝ) * HLm Γ 5 L11242 + (-1 : ℝ) * HLm Γ 5 L11244 := by
  have h := HLm_submod hΓ [F16] L11245 [F23]
  rw [show [F16] ++ L11245 ++ [F23] = L11243 from rfl, show [F16] ++ L11245 = L11239 from rfl,
    show L11245 ++ [F23] = L11241 from rfl] at h
  rw [i6888 hinj, i6886 hinj, i6887 hinj, i6889 hinj] at h
  linarith

theorem row2321 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11246 + (1 : ℝ) * HLm Γ 5 L3279 + (-1 : ℝ) * HLm Γ 5 L11103 + (-1 : ℝ) * HLm Γ 5 L11250 := by
  have h := HLm_submod hΓ [F1] L11251 [F10]
  rw [show [F1] ++ L11251 ++ [F10] = L11249 from rfl, show [F1] ++ L11251 = L11247 from rfl,
    show L11251 ++ [F10] = L11248 from rfl] at h
  rw [i6892 hinj, i6890 hinj, i6891 hinj, i6893 hinj] at h
  linarith

theorem row2322 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11252 + (1 : ℝ) * HLm Γ 5 L11254 + (-1 : ℝ) * HLm Γ 5 L11256 + (-1 : ℝ) * HLm Γ 5 L11258 := by
  have h := HLm_submod hΓ [F0] L11259 [F3]
  rw [show [F0] ++ L11259 ++ [F3] = L11257 from rfl, show [F0] ++ L11259 = L11253 from rfl,
    show L11259 ++ [F3] = L11255 from rfl] at h
  rw [i6896 hinj, i6894 hinj, i6895 hinj, i6897 hinj] at h
  linarith

theorem row2323 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11260 + (1 : ℝ) * HLm Γ 5 L11262 + (-1 : ℝ) * HLm Γ 5 L11264 + (-1 : ℝ) * HLm Γ 5 L11266 := by
  have h := HLm_submod hΓ [F62] L11267 [F210]
  rw [show [F62] ++ L11267 ++ [F210] = L11265 from rfl, show [F62] ++ L11267 = L11261 from rfl,
    show L11267 ++ [F210] = L11263 from rfl] at h
  rw [i6900 hinj, i6898 hinj, i6899 hinj, i6901 hinj] at h
  linarith

theorem row2324 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11268 + (1 : ℝ) * HLm Γ 5 L11270 + (-1 : ℝ) * HLm Γ 5 L11272 + (-1 : ℝ) * HLm Γ 5 L11274 := by
  have h := HLm_submod hΓ [F7] L11274 [F12]
  rw [show [F7] ++ L11274 ++ [F12] = L11273 from rfl, show [F7] ++ L11274 = L11269 from rfl,
    show L11274 ++ [F12] = L11271 from rfl] at h
  rw [i6904 hinj, i6902 hinj, i6903 hinj] at h
  linarith

theorem row2325 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5700 + (1 : ℝ) * HLm Γ 5 L11276 + (-1 : ℝ) * HLm Γ 5 L11038 + (-1 : ℝ) * HLm Γ 5 L11117 := by
  have h := HLm_submod hΓ [F7] L11117 [F12]
  rw [show [F7] ++ L11117 ++ [F12] = L11278 from rfl, show [F7] ++ L11117 = L11275 from rfl,
    show L11117 ++ [F12] = L11277 from rfl] at h
  rw [i6907 hinj, i6905 hinj, i6906 hinj] at h
  linarith

theorem row2326 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1418 + (1 : ℝ) * HLm Γ 5 L11280 + (-1 : ℝ) * HLm Γ 5 L11282 + (-1 : ℝ) * HLm Γ 5 L3323 := by
  have h := HLm_submod hΓ [F16] L3323 [F236]
  rw [show [F16] ++ L3323 ++ [F236] = L11283 from rfl, show [F16] ++ L3323 = L11279 from rfl,
    show L3323 ++ [F236] = L11281 from rfl] at h
  rw [i6910 hinj, i6908 hinj, i6909 hinj] at h
  linarith

theorem row2327 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11284 + (1 : ℝ) * HLm Γ 5 L4884 + (-1 : ℝ) * HLm Γ 5 L11286 + (-1 : ℝ) * HLm Γ 5 L11288 := by
  have h := HLm_submod hΓ [F12] L11289 [F45]
  rw [show [F12] ++ L11289 ++ [F45] = L11287 from rfl, show [F12] ++ L11289 = L11285 from rfl,
    show L11289 ++ [F45] = L4885 from rfl] at h
  rw [i6912 hinj, i6911 hinj, i2749 hinj, i6913 hinj] at h
  linarith

theorem row2328 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11290 + (1 : ℝ) * HLm Γ 5 L11292 + (-1 : ℝ) * HLm Γ 5 L11294 + (-1 : ℝ) * HLm Γ 5 L467 := by
  have h := HLm_submod hΓ [F210] L11296 [F25]
  rw [show [F210] ++ L11296 ++ [F25] = L11295 from rfl, show [F210] ++ L11296 = L11291 from rfl,
    show L11296 ++ [F25] = L11293 from rfl] at h
  rw [i6916 hinj, i6914 hinj, i6915 hinj, i6917 hinj] at h
  linarith

theorem row2329 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4252 + (1 : ℝ) * HLm Γ 5 L11099 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L11096 := by
  have h := HLm_submod hΓ [F0] L11300 [F9]
  rw [show [F0] ++ L11300 ++ [F9] = L11299 from rfl, show [F0] ++ L11300 = L11297 from rfl,
    show L11300 ++ [F9] = L11298 from rfl] at h
  rw [i6920 hinj, i6918 hinj, i6919 hinj, i6921 hinj] at h
  linarith

theorem row2330 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1716 + (1 : ℝ) * HLm Γ 5 L9478 + (-1 : ℝ) * HLm Γ 5 L5188 + (-1 : ℝ) * HLm Γ 5 L11304 := by
  have h := HLm_submod hΓ [F22] L11305 [F228]
  rw [show [F22] ++ L11305 ++ [F228] = L11303 from rfl, show [F22] ++ L11305 = L11301 from rfl,
    show L11305 ++ [F228] = L11302 from rfl] at h
  rw [i6924 hinj, i6922 hinj, i6923 hinj, i6925 hinj] at h
  linarith

theorem row2331 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10049 + (1 : ℝ) * HLm Γ 5 L11307 + (-1 : ℝ) * HLm Γ 5 L10043 + (-1 : ℝ) * HLm Γ 5 L11310 := by
  have h := HLm_submod hΓ [F2] L11311 [F210]
  rw [show [F2] ++ L11311 ++ [F210] = L11309 from rfl, show [F2] ++ L11311 = L11306 from rfl,
    show L11311 ++ [F210] = L11308 from rfl] at h
  rw [i6928 hinj, i6926 hinj, i6927 hinj, i6929 hinj] at h
  linarith

theorem row2332 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11194 + (1 : ℝ) * HLm Γ 5 L11312 + (-1 : ℝ) * HLm Γ 5 L11191 + (-1 : ℝ) * HLm Γ 5 L11315 := by
  have h := HLm_submod hΓ [F5] L11316 [F105]
  rw [show [F5] ++ L11316 ++ [F105] = L11314 from rfl, show [F5] ++ L11316 = L11195 from rfl,
    show L11316 ++ [F105] = L11313 from rfl] at h
  rw [i6931 hinj, i6863 hinj, i6930 hinj, i6932 hinj] at h
  linarith

theorem row2333 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11317 + (1 : ℝ) * HLm Γ 5 L11155 + (-1 : ℝ) * HLm Γ 5 L11320 + (-1 : ℝ) * HLm Γ 5 L11322 := by
  have h := HLm_submod hΓ [F10] L11323 [F43]
  rw [show [F10] ++ L11323 ++ [F43] = L11321 from rfl, show [F10] ++ L11323 = L11318 from rfl,
    show L11323 ++ [F43] = L11319 from rfl] at h
  rw [i6935 hinj, i6933 hinj, i6934 hinj, i6936 hinj] at h
  linarith

theorem row2334 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11324 + (1 : ℝ) * HLm Γ 5 L11250 + (-1 : ℝ) * HLm Γ 5 L11246 + (-1 : ℝ) * HLm Γ 5 L11325 := by
  have h := HLm_submod hΓ [F1] L11325 [F41]
  rw [show [F1] ++ L11325 ++ [F41] = L11247 from rfl, show [F1] ++ L11325 = L11324 from rfl,
    show L11325 ++ [F41] = L11251 from rfl] at h
  rw [i6890 hinj, i6893 hinj] at h
  linarith

theorem row2335 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L989 + (1 : ℝ) * HLm Γ 5 L11327 + (-1 : ℝ) * HLm Γ 5 L5487 + (-1 : ℝ) * HLm Γ 5 L11330 := by
  have h := HLm_submod hΓ [F0] L11331 [F210]
  rw [show [F0] ++ L11331 ++ [F210] = L11329 from rfl, show [F0] ++ L11331 = L11326 from rfl,
    show L11331 ++ [F210] = L11328 from rfl] at h
  rw [i6939 hinj, i6937 hinj, i6938 hinj, i6940 hinj] at h
  linarith

theorem row2336 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L11333 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L11336 := by
  have h := HLm_submod hΓ [F12] L11337 [F210]
  rw [show [F12] ++ L11337 ++ [F210] = L11335 from rfl, show [F12] ++ L11337 = L11332 from rfl,
    show L11337 ++ [F210] = L11334 from rfl] at h
  rw [i6943 hinj, i6941 hinj, i6942 hinj, i6944 hinj] at h
  linarith

theorem row2337 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2055 + (1 : ℝ) * HLm Γ 5 L11338 + (-1 : ℝ) * HLm Γ 5 L11340 + (-1 : ℝ) * HLm Γ 5 L2053 := by
  have h := HLm_submod hΓ [F3] L2054 [F399]
  rw [show [F3] ++ L2054 ++ [F399] = L11341 from rfl, show [F3] ++ L2054 = L2056 from rfl,
    show L2054 ++ [F399] = L11339 from rfl] at h
  rw [i6946 hinj, i1127 hinj, i6945 hinj, i1126 hinj] at h
  linarith

theorem row2338 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L644 + (1 : ℝ) * HLm Γ 5 L11343 + (-1 : ℝ) * HLm Γ 5 L11344 + (-1 : ℝ) * HLm Γ 5 L11346 := by
  have h := HLm_submod hΓ [F7] L11346 [F210]
  rw [show [F7] ++ L11346 ++ [F210] = L11345 from rfl, show [F7] ++ L11346 = L11342 from rfl,
    show L11346 ++ [F210] = L11343 from rfl] at h
  rw [i6948 hinj, i6947 hinj] at h
  linarith

theorem row2339 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11347 + (1 : ℝ) * HLm Γ 5 L11349 + (-1 : ℝ) * HLm Γ 5 L11351 + (-1 : ℝ) * HLm Γ 5 L11353 := by
  have h := HLm_submod hΓ [F210] L11353 [F14]
  rw [show [F210] ++ L11353 ++ [F14] = L11352 from rfl, show [F210] ++ L11353 = L11348 from rfl,
    show L11353 ++ [F14] = L11350 from rfl] at h
  rw [i6951 hinj, i6949 hinj, i6950 hinj] at h
  linarith

theorem row2340 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11354 + (1 : ℝ) * HLm Γ 5 L11356 + (-1 : ℝ) * HLm Γ 5 L11358 + (-1 : ℝ) * HLm Γ 5 L11360 := by
  have h := HLm_submod hΓ [F210] L11361 [F43]
  rw [show [F210] ++ L11361 ++ [F43] = L11359 from rfl, show [F210] ++ L11361 = L11355 from rfl,
    show L11361 ++ [F43] = L11357 from rfl] at h
  rw [i6954 hinj, i6952 hinj, i6953 hinj, i6955 hinj] at h
  linarith

theorem row2341 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L11363 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L11366 := by
  have h := HLm_submod hΓ [F10] L11367 [F210]
  rw [show [F10] ++ L11367 ++ [F210] = L11365 from rfl, show [F10] ++ L11367 = L11362 from rfl,
    show L11367 ++ [F210] = L11364 from rfl] at h
  rw [i6958 hinj, i6956 hinj, i6957 hinj, i6959 hinj] at h
  linarith

theorem row2342 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11368 + (1 : ℝ) * HLm Γ 5 L11330 + (-1 : ℝ) * HLm Γ 5 L11327 + (-1 : ℝ) * HLm Γ 5 L11372 := by
  have h := HLm_submod hΓ [F210] L11373 [F27]
  rw [show [F210] ++ L11373 ++ [F27] = L11371 from rfl, show [F210] ++ L11373 = L11369 from rfl,
    show L11373 ++ [F27] = L11370 from rfl] at h
  rw [i6962 hinj, i6960 hinj, i6961 hinj, i6963 hinj] at h
  linarith

theorem row2343 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2505 + (1 : ℝ) * HLm Γ 5 L11375 + (-1 : ℝ) * HLm Γ 5 L11377 + (-1 : ℝ) * HLm Γ 5 L11379 := by
  have h := HLm_submod hΓ [F47] L11380 [F210]
  rw [show [F47] ++ L11380 ++ [F210] = L11378 from rfl, show [F47] ++ L11380 = L11374 from rfl,
    show L11380 ++ [F210] = L11376 from rfl] at h
  rw [i6966 hinj, i6964 hinj, i6965 hinj, i6967 hinj] at h
  linarith

theorem row2344 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11381 + (1 : ℝ) * HLm Γ 5 L11383 + (-1 : ℝ) * HLm Γ 5 L11385 + (-1 : ℝ) * HLm Γ 5 L11387 := by
  have h := HLm_submod hΓ [F2] L11388 [F210]
  rw [show [F2] ++ L11388 ++ [F210] = L11386 from rfl, show [F2] ++ L11388 = L11382 from rfl,
    show L11388 ++ [F210] = L11384 from rfl] at h
  rw [i6970 hinj, i6968 hinj, i6969 hinj, i6971 hinj] at h
  linarith

theorem row2345 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L842 + (1 : ℝ) * HLm Γ 5 L11390 + (-1 : ℝ) * HLm Γ 5 L5381 + (-1 : ℝ) * HLm Γ 5 L11393 := by
  have h := HLm_submod hΓ [F0] L11394 [F210]
  rw [show [F0] ++ L11394 ++ [F210] = L11392 from rfl, show [F0] ++ L11394 = L11389 from rfl,
    show L11394 ++ [F210] = L11391 from rfl] at h
  rw [i6974 hinj, i6972 hinj, i6973 hinj, i6975 hinj] at h
  linarith

theorem row2346 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6897 + (1 : ℝ) * HLm Γ 5 L194 + (-1 : ℝ) * HLm Γ 5 L11395 + (-1 : ℝ) * HLm Γ 5 L199 := by
  have h := HLm_submod hΓ [F210] L199 [F17]
  rw [show [F210] ++ L199 ++ [F17] = L11396 from rfl, show [F210] ++ L199 = L6898 from rfl,
    show L199 ++ [F17] = L902 from rfl] at h
  rw [i6976 hinj, i4102 hinj, i412 hinj] at h
  linarith

theorem row2347 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11397 + (1 : ℝ) * HLm Γ 5 L11399 + (-1 : ℝ) * HLm Γ 5 L11401 + (-1 : ℝ) * HLm Γ 5 L11403 := by
  have h := HLm_submod hΓ [F67] L11404 [F210]
  rw [show [F67] ++ L11404 ++ [F210] = L11402 from rfl, show [F67] ++ L11404 = L11398 from rfl,
    show L11404 ++ [F210] = L11400 from rfl] at h
  rw [i6979 hinj, i6977 hinj, i6978 hinj, i6980 hinj] at h
  linarith

theorem row2348 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4558 + (1 : ℝ) * HLm Γ 5 L11406 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L11409 := by
  have h := HLm_submod hΓ [F0] L11410 [F67]
  rw [show [F0] ++ L11410 ++ [F67] = L11408 from rfl, show [F0] ++ L11410 = L11405 from rfl,
    show L11410 ++ [F67] = L11407 from rfl] at h
  rw [i6983 hinj, i6981 hinj, i6982 hinj, i6984 hinj] at h
  linarith

theorem row2349 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11360 + (1 : ℝ) * HLm Γ 5 L11412 + (-1 : ℝ) * HLm Γ 5 L11354 + (-1 : ℝ) * HLm Γ 5 L11415 := by
  have h := HLm_submod hΓ [F111] L11416 [F210]
  rw [show [F111] ++ L11416 ++ [F210] = L11414 from rfl, show [F111] ++ L11416 = L11411 from rfl,
    show L11416 ++ [F210] = L11413 from rfl] at h
  rw [i6987 hinj, i6985 hinj, i6986 hinj, i6988 hinj] at h
  linarith

theorem row2350 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11417 + (1 : ℝ) * HLm Γ 5 L11419 + (-1 : ℝ) * HLm Γ 5 L11421 + (-1 : ℝ) * HLm Γ 5 L7223 := by
  have h := HLm_submod hΓ [F210] L7223 [F42]
  rw [show [F210] ++ L7223 ++ [F42] = L11422 from rfl, show [F210] ++ L7223 = L11418 from rfl,
    show L7223 ++ [F42] = L11420 from rfl] at h
  rw [i6991 hinj, i6989 hinj, i6990 hinj] at h
  linarith

theorem row2351 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11423 + (1 : ℝ) * HLm Γ 5 L11425 + (-1 : ℝ) * HLm Γ 5 L11427 + (-1 : ℝ) * HLm Γ 5 L11429 := by
  have h := HLm_submod hΓ [F210] L11430 [F19]
  rw [show [F210] ++ L11430 ++ [F19] = L11428 from rfl, show [F210] ++ L11430 = L11424 from rfl,
    show L11430 ++ [F19] = L11426 from rfl] at h
  rw [i6994 hinj, i6992 hinj, i6993 hinj, i6995 hinj] at h
  linarith

theorem row2352 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11431 + (1 : ℝ) * HLm Γ 5 L11433 + (-1 : ℝ) * HLm Γ 5 L11435 + (-1 : ℝ) * HLm Γ 5 L11437 := by
  have h := HLm_submod hΓ [F1] L11438 [F210]
  rw [show [F1] ++ L11438 ++ [F210] = L11436 from rfl, show [F1] ++ L11438 = L11432 from rfl,
    show L11438 ++ [F210] = L11434 from rfl] at h
  rw [i6998 hinj, i6996 hinj, i6997 hinj, i6999 hinj] at h
  linarith

theorem row2353 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11180 + (1 : ℝ) * HLm Γ 5 L11440 + (-1 : ℝ) * HLm Γ 5 L11442 + (-1 : ℝ) * HLm Γ 5 L11444 := by
  have h := HLm_submod hΓ [F67] L11445 [F25]
  rw [show [F67] ++ L11445 ++ [F25] = L11443 from rfl, show [F67] ++ L11445 = L11439 from rfl,
    show L11445 ++ [F25] = L11441 from rfl] at h
  rw [i7002 hinj, i7000 hinj, i7001 hinj, i7003 hinj] at h
  linarith

theorem row2354 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11446 + (1 : ℝ) * HLm Γ 5 L11448 + (-1 : ℝ) * HLm Γ 5 L11449 + (-1 : ℝ) * HLm Γ 5 L136 := by
  have h := HLm_submod hΓ [F210] L136 [F66]
  rw [show [F210] ++ L136 ++ [F66] = L11450 from rfl, show [F210] ++ L136 = L11447 from rfl,
    show L136 ++ [F66] = L11448 from rfl] at h
  rw [i7005 hinj, i7004 hinj] at h
  linarith

theorem row2355 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11451 + (1 : ℝ) * HLm Γ 5 L11453 + (-1 : ℝ) * HLm Γ 5 L11455 + (-1 : ℝ) * HLm Γ 5 L11457 := by
  have h := HLm_submod hΓ [F9] L11458 [F55]
  rw [show [F9] ++ L11458 ++ [F55] = L11456 from rfl, show [F9] ++ L11458 = L11452 from rfl,
    show L11458 ++ [F55] = L11454 from rfl] at h
  rw [i7008 hinj, i7006 hinj, i7007 hinj, i7009 hinj] at h
  linarith

theorem row2356 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11459 + (1 : ℝ) * HLm Γ 5 L11461 + (-1 : ℝ) * HLm Γ 5 L11463 + (-1 : ℝ) * HLm Γ 5 L11465 := by
  have h := HLm_submod hΓ [F108] L11466 [F211]
  rw [show [F108] ++ L11466 ++ [F211] = L11464 from rfl, show [F108] ++ L11466 = L11460 from rfl,
    show L11466 ++ [F211] = L11462 from rfl] at h
  rw [i7012 hinj, i7010 hinj, i7011 hinj, i7013 hinj] at h
  linarith

theorem row2357 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11467 + (1 : ℝ) * HLm Γ 5 L11294 + (-1 : ℝ) * HLm Γ 5 L11470 + (-1 : ℝ) * HLm Γ 5 L11292 := by
  have h := HLm_submod hΓ [F47] L11472 [F210]
  rw [show [F47] ++ L11472 ++ [F210] = L11471 from rfl, show [F47] ++ L11472 = L11468 from rfl,
    show L11472 ++ [F210] = L11469 from rfl] at h
  rw [i7016 hinj, i7014 hinj, i7015 hinj, i7017 hinj] at h
  linarith

theorem row2358 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11473 + (1 : ℝ) * HLm Γ 5 L11475 + (-1 : ℝ) * HLm Γ 5 L11477 + (-1 : ℝ) * HLm Γ 5 L11479 := by
  have h := HLm_submod hΓ [F1] L11480 [F26]
  rw [show [F1] ++ L11480 ++ [F26] = L11478 from rfl, show [F1] ++ L11480 = L11474 from rfl,
    show L11480 ++ [F26] = L11476 from rfl] at h
  rw [i7020 hinj, i7018 hinj, i7019 hinj, i7021 hinj] at h
  linarith

theorem row2359 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3065 + (1 : ℝ) * HLm Γ 5 L3136 + (-1 : ℝ) * HLm Γ 5 L11481 + (-1 : ℝ) * HLm Γ 5 L332 := by
  have h := HLm_submod hΓ [F210] L332 [F96]
  rw [show [F210] ++ L332 ++ [F96] = L11482 from rfl, show [F210] ++ L332 = L3066 from rfl,
    show L332 ++ [F96] = L4126 from rfl] at h
  rw [i7022 hinj, i1744 hinj, i2303 hinj] at h
  linarith

theorem row2360 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1278 + (1 : ℝ) * HLm Γ 5 L11484 + (-1 : ℝ) * HLm Γ 5 L5502 + (-1 : ℝ) * HLm Γ 5 L11487 := by
  have h := HLm_submod hΓ [F4] L11488 [F228]
  rw [show [F4] ++ L11488 ++ [F228] = L11486 from rfl, show [F4] ++ L11488 = L11483 from rfl,
    show L11488 ++ [F228] = L11485 from rfl] at h
  rw [i7025 hinj, i7023 hinj, i7024 hinj, i7026 hinj] at h
  linarith

theorem row2361 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1278 + (1 : ℝ) * HLm Γ 5 L11490 + (-1 : ℝ) * HLm Γ 5 L4252 + (-1 : ℝ) * HLm Γ 5 L11493 := by
  have h := HLm_submod hΓ [F4] L11494 [F210]
  rw [show [F4] ++ L11494 ++ [F210] = L11492 from rfl, show [F4] ++ L11494 = L11489 from rfl,
    show L11494 ++ [F210] = L11491 from rfl] at h
  rw [i7029 hinj, i7027 hinj, i7028 hinj, i7030 hinj] at h
  linarith

theorem row2362 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11395 + (1 : ℝ) * HLm Γ 5 L197 + (-1 : ℝ) * HLm Γ 5 L11495 + (-1 : ℝ) * HLm Γ 5 L194 := by
  have h := HLm_submod hΓ [F210] L902 [F45]
  rw [show [F210] ++ L902 ++ [F45] = L11496 from rfl, show [F210] ++ L902 = L11396 from rfl,
    show L902 ++ [F45] = L899 from rfl] at h
  rw [i7031 hinj, i6976 hinj, i410 hinj, i412 hinj] at h
  linarith

theorem row2363 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11497 + (1 : ℝ) * HLm Γ 5 L11499 + (-1 : ℝ) * HLm Γ 5 L11501 + (-1 : ℝ) * HLm Γ 5 L11503 := by
  have h := HLm_submod hΓ [F210] L11504 [F34]
  rw [show [F210] ++ L11504 ++ [F34] = L11502 from rfl, show [F210] ++ L11504 = L11498 from rfl,
    show L11504 ++ [F34] = L11500 from rfl] at h
  rw [i7034 hinj, i7032 hinj, i7033 hinj, i7035 hinj] at h
  linarith

theorem row2364 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1594 + (1 : ℝ) * HLm Γ 5 L11505 + (-1 : ℝ) * HLm Γ 5 L11507 + (-1 : ℝ) * HLm Γ 5 L2971 := by
  have h := HLm_submod hΓ [F9] L2972 [F217]
  rw [show [F9] ++ L2972 ++ [F217] = L11508 from rfl, show [F9] ++ L2972 = L1595 from rfl,
    show L2972 ++ [F217] = L11506 from rfl] at h
  rw [i7037 hinj, i817 hinj, i7036 hinj, i1694 hinj] at h
  linarith

theorem row2365 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1583 + (1 : ℝ) * HLm Γ 5 L11509 + (-1 : ℝ) * HLm Γ 5 L11511 + (-1 : ℝ) * HLm Γ 5 L11513 := by
  have h := HLm_submod hΓ [F9] L11514 [F217]
  rw [show [F9] ++ L11514 ++ [F217] = L11512 from rfl, show [F9] ++ L11514 = L1584 from rfl,
    show L11514 ++ [F217] = L11510 from rfl] at h
  rw [i7039 hinj, i811 hinj, i7038 hinj, i7040 hinj] at h
  linarith

theorem row2366 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11515 + (1 : ℝ) * HLm Γ 5 L11517 + (-1 : ℝ) * HLm Γ 5 L11519 + (-1 : ℝ) * HLm Γ 5 L11521 := by
  have h := HLm_submod hΓ [F3] L11522 [F67]
  rw [show [F3] ++ L11522 ++ [F67] = L11520 from rfl, show [F3] ++ L11522 = L11516 from rfl,
    show L11522 ++ [F67] = L11518 from rfl] at h
  rw [i7043 hinj, i7041 hinj, i7042 hinj, i7044 hinj] at h
  linarith

theorem row2367 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11523 + (1 : ℝ) * HLm Γ 5 L11525 + (-1 : ℝ) * HLm Γ 5 L11527 + (-1 : ℝ) * HLm Γ 5 L11529 := by
  have h := HLm_submod hΓ [F210] L11530 [F25]
  rw [show [F210] ++ L11530 ++ [F25] = L11528 from rfl, show [F210] ++ L11530 = L11524 from rfl,
    show L11530 ++ [F25] = L11526 from rfl] at h
  rw [i7047 hinj, i7045 hinj, i7046 hinj, i7048 hinj] at h
  linarith

theorem row2368 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11477 + (1 : ℝ) * HLm Γ 5 L11531 + (-1 : ℝ) * HLm Γ 5 L6520 + (-1 : ℝ) * HLm Γ 5 L11475 := by
  have h := HLm_submod hΓ [F1] L11476 [F16]
  rw [show [F1] ++ L11476 ++ [F16] = L11533 from rfl, show [F1] ++ L11476 = L11478 from rfl,
    show L11476 ++ [F16] = L11532 from rfl] at h
  rw [i7050 hinj, i7020 hinj, i7049 hinj, i7019 hinj] at h
  linarith

theorem row2369 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11534 + (1 : ℝ) * HLm Γ 5 L11536 + (-1 : ℝ) * HLm Γ 5 L11538 + (-1 : ℝ) * HLm Γ 5 L11540 := by
  have h := HLm_submod hΓ [F5] L11541 [F210]
  rw [show [F5] ++ L11541 ++ [F210] = L11539 from rfl, show [F5] ++ L11541 = L11535 from rfl,
    show L11541 ++ [F210] = L11537 from rfl] at h
  rw [i7053 hinj, i7051 hinj, i7052 hinj, i7054 hinj] at h
  linarith

theorem row2370 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11542 + (1 : ℝ) * HLm Γ 5 L11465 + (-1 : ℝ) * HLm Γ 5 L11461 + (-1 : ℝ) * HLm Γ 5 L11546 := by
  have h := HLm_submod hΓ [F211] L11547 [F43]
  rw [show [F211] ++ L11547 ++ [F43] = L11545 from rfl, show [F211] ++ L11547 = L11543 from rfl,
    show L11547 ++ [F43] = L11544 from rfl] at h
  rw [i7057 hinj, i7055 hinj, i7056 hinj, i7058 hinj] at h
  linarith

theorem row2371 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11548 + (1 : ℝ) * HLm Γ 5 L11550 + (-1 : ℝ) * HLm Γ 5 L11552 + (-1 : ℝ) * HLm Γ 5 L11554 := by
  have h := HLm_submod hΓ [F25] L11555 [F48]
  rw [show [F25] ++ L11555 ++ [F48] = L11553 from rfl, show [F25] ++ L11555 = L11549 from rfl,
    show L11555 ++ [F48] = L11551 from rfl] at h
  rw [i7061 hinj, i7059 hinj, i7060 hinj, i7062 hinj] at h
  linarith

theorem row2372 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3517 + (1 : ℝ) * HLm Γ 5 L11557 + (-1 : ℝ) * HLm Γ 5 L5381 + (-1 : ℝ) * HLm Γ 5 L11560 := by
  have h := HLm_submod hΓ [F0] L11561 [F210]
  rw [show [F0] ++ L11561 ++ [F210] = L11559 from rfl, show [F0] ++ L11561 = L11556 from rfl,
    show L11561 ++ [F210] = L11558 from rfl] at h
  rw [i7065 hinj, i7063 hinj, i7064 hinj, i7066 hinj] at h
  linarith

theorem row2373 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11562 + (1 : ℝ) * HLm Γ 5 L11564 + (-1 : ℝ) * HLm Γ 5 L5489 + (-1 : ℝ) * HLm Γ 5 L11567 := by
  have h := HLm_submod hΓ [F0] L11568 [F16]
  rw [show [F0] ++ L11568 ++ [F16] = L11566 from rfl, show [F0] ++ L11568 = L11563 from rfl,
    show L11568 ++ [F16] = L11565 from rfl] at h
  rw [i7069 hinj, i7067 hinj, i7068 hinj, i7070 hinj] at h
  linarith

theorem row2374 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11569 + (1 : ℝ) * HLm Γ 5 L11571 + (-1 : ℝ) * HLm Γ 5 L11280 + (-1 : ℝ) * HLm Γ 5 L11573 := by
  have h := HLm_submod hΓ [F3] L11573 [F45]
  rw [show [F3] ++ L11573 ++ [F45] = L11572 from rfl, show [F3] ++ L11573 = L11570 from rfl,
    show L11573 ++ [F45] = L11571 from rfl] at h
  rw [i7072 hinj, i7071 hinj] at h
  linarith

theorem row2375 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11393 + (1 : ℝ) * HLm Γ 5 L11495 + (-1 : ℝ) * HLm Γ 5 L11390 + (-1 : ℝ) * HLm Γ 5 L197 := by
  have h := HLm_submod hΓ [F51] L899 [F210]
  rw [show [F51] ++ L899 ++ [F210] = L11391 from rfl, show [F51] ++ L899 = L11394 from rfl,
    show L899 ++ [F210] = L11574 from rfl] at h
  rw [i6973 hinj, i6975 hinj, i7073 hinj, i410 hinj] at h
  linarith

theorem row2376 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11575 + (1 : ℝ) * HLm Γ 5 L11577 + (-1 : ℝ) * HLm Γ 5 L11579 + (-1 : ℝ) * HLm Γ 5 L3112 := by
  have h := HLm_submod hΓ [F210] L11581 [F29]
  rw [show [F210] ++ L11581 ++ [F29] = L11580 from rfl, show [F210] ++ L11581 = L11576 from rfl,
    show L11581 ++ [F29] = L11578 from rfl] at h
  rw [i7076 hinj, i7074 hinj, i7075 hinj, i7077 hinj] at h
  linarith

theorem row2377 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11582 + (1 : ℝ) * HLm Γ 5 L11442 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L11440 := by
  have h := HLm_submod hΓ [F0] L11441 [F67]
  rw [show [F0] ++ L11441 ++ [F67] = L11585 from rfl, show [F0] ++ L11441 = L11583 from rfl,
    show L11441 ++ [F67] = L11584 from rfl] at h
  rw [i7080 hinj, i7078 hinj, i7079 hinj, i7001 hinj] at h
  linarith

theorem row2378 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11586 + (1 : ℝ) * HLm Γ 5 L11564 + (-1 : ℝ) * HLm Γ 5 L6066 + (-1 : ℝ) * HLm Γ 5 L11567 := by
  have h := HLm_submod hΓ [F1] L11568 [F16]
  rw [show [F1] ++ L11568 ++ [F16] = L11588 from rfl, show [F1] ++ L11568 = L11587 from rfl,
    show L11568 ++ [F16] = L11565 from rfl] at h
  rw [i7082 hinj, i7081 hinj, i7068 hinj, i7070 hinj] at h
  linarith

theorem row2379 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11444 + (1 : ℝ) * HLm Γ 5 L11590 + (-1 : ℝ) * HLm Γ 5 L11440 + (-1 : ℝ) * HLm Γ 5 L3700 := by
  have h := HLm_submod hΓ [F16] L3701 [F25]
  rw [show [F16] ++ L3701 ++ [F25] = L11592 from rfl, show [F16] ++ L3701 = L11589 from rfl,
    show L3701 ++ [F25] = L11591 from rfl] at h
  rw [i7085 hinj, i7083 hinj, i7084 hinj, i2071 hinj] at h
  linarith

theorem row2380 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11593 + (1 : ℝ) * HLm Γ 5 L11595 + (-1 : ℝ) * HLm Γ 5 L11597 + (-1 : ℝ) * HLm Γ 5 L11599 := by
  have h := HLm_submod hΓ [F16] L11600 [F211]
  rw [show [F16] ++ L11600 ++ [F211] = L11598 from rfl, show [F16] ++ L11600 = L11594 from rfl,
    show L11600 ++ [F211] = L11596 from rfl] at h
  rw [i7088 hinj, i7086 hinj, i7087 hinj, i7089 hinj] at h
  linarith

theorem row2381 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11601 + (1 : ℝ) * HLm Γ 5 L11603 + (-1 : ℝ) * HLm Γ 5 L11605 + (-1 : ℝ) * HLm Γ 5 L11607 := by
  have h := HLm_submod hΓ [F107] L11608 [F210]
  rw [show [F107] ++ L11608 ++ [F210] = L11606 from rfl, show [F107] ++ L11608 = L11602 from rfl,
    show L11608 ++ [F210] = L11604 from rfl] at h
  rw [i7092 hinj, i7090 hinj, i7091 hinj, i7093 hinj] at h
  linarith

theorem row2382 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L11610 + (-1 : ℝ) * HLm Γ 5 L11582 + (-1 : ℝ) * HLm Γ 5 L11613 := by
  have h := HLm_submod hΓ [F0] L11614 [F210]
  rw [show [F0] ++ L11614 ++ [F210] = L11612 from rfl, show [F0] ++ L11614 = L11609 from rfl,
    show L11614 ++ [F210] = L11611 from rfl] at h
  rw [i7096 hinj, i7094 hinj, i7095 hinj, i7097 hinj] at h
  linarith

theorem row2383 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5927 + (1 : ℝ) * HLm Γ 5 L11511 + (-1 : ℝ) * HLm Γ 5 L6089 + (-1 : ℝ) * HLm Γ 5 L11509 := by
  have h := HLm_submod hΓ [F1] L11510 [F9]
  rw [show [F1] ++ L11510 ++ [F9] = L11617 from rfl, show [F1] ++ L11510 = L11615 from rfl,
    show L11510 ++ [F9] = L11616 from rfl] at h
  rw [i7100 hinj, i7098 hinj, i7099 hinj, i7038 hinj] at h
  linarith

theorem row2384 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11618 + (1 : ℝ) * HLm Γ 5 L11579 + (-1 : ℝ) * HLm Γ 5 L11621 + (-1 : ℝ) * HLm Γ 5 L11577 := by
  have h := HLm_submod hΓ [F7] L11578 [F210]
  rw [show [F7] ++ L11578 ++ [F210] = L11622 from rfl, show [F7] ++ L11578 = L11619 from rfl,
    show L11578 ++ [F210] = L11620 from rfl] at h
  rw [i7103 hinj, i7101 hinj, i7102 hinj, i7075 hinj] at h
  linarith

theorem row2385 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L260 + (1 : ℝ) * HLm Γ 5 L11624 + (-1 : ℝ) * HLm Γ 5 L11626 + (-1 : ℝ) * HLm Γ 5 L11628 := by
  have h := HLm_submod hΓ [F0] L11629 [F210]
  rw [show [F0] ++ L11629 ++ [F210] = L11627 from rfl, show [F0] ++ L11629 = L11623 from rfl,
    show L11629 ++ [F210] = L11625 from rfl] at h
  rw [i7106 hinj, i7104 hinj, i7105 hinj, i7107 hinj] at h
  linarith

theorem row2386 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5384 + (1 : ℝ) * HLm Γ 5 L11552 + (-1 : ℝ) * HLm Γ 5 L11632 + (-1 : ℝ) * HLm Γ 5 L11548 := by
  have h := HLm_submod hΓ [F1] L11634 [F48]
  rw [show [F1] ++ L11634 ++ [F48] = L11633 from rfl, show [F1] ++ L11634 = L11630 from rfl,
    show L11634 ++ [F48] = L11631 from rfl] at h
  rw [i7110 hinj, i7108 hinj, i7109 hinj, i7111 hinj] at h
  linarith

theorem row2387 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11635 + (1 : ℝ) * HLm Γ 5 L11637 + (-1 : ℝ) * HLm Γ 5 L11639 + (-1 : ℝ) * HLm Γ 5 L11641 := by
  have h := HLm_submod hΓ [F0] L11642 [F219]
  rw [show [F0] ++ L11642 ++ [F219] = L11640 from rfl, show [F0] ++ L11642 = L11636 from rfl,
    show L11642 ++ [F219] = L11638 from rfl] at h
  rw [i7114 hinj, i7112 hinj, i7113 hinj, i7115 hinj] at h
  linarith

theorem row2388 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11643 + (1 : ℝ) * HLm Γ 5 L11645 + (-1 : ℝ) * HLm Γ 5 L11647 + (-1 : ℝ) * HLm Γ 5 L11649 := by
  have h := HLm_submod hΓ [F210] L11650 [F26]
  rw [show [F210] ++ L11650 ++ [F26] = L11648 from rfl, show [F210] ++ L11650 = L11644 from rfl,
    show L11650 ++ [F26] = L11646 from rfl] at h
  rw [i7118 hinj, i7116 hinj, i7117 hinj, i7119 hinj] at h
  linarith

theorem row2389 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9555 + (1 : ℝ) * HLm Γ 5 L11652 + (-1 : ℝ) * HLm Γ 5 L11654 + (-1 : ℝ) * HLm Γ 5 L11656 := by
  have h := HLm_submod hΓ [F1] L11657 [F111]
  rw [show [F1] ++ L11657 ++ [F111] = L11655 from rfl, show [F1] ++ L11657 = L11651 from rfl,
    show L11657 ++ [F111] = L11653 from rfl] at h
  rw [i7122 hinj, i7120 hinj, i7121 hinj, i7123 hinj] at h
  linarith

theorem row2390 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11658 + (1 : ℝ) * HLm Γ 5 L11660 + (-1 : ℝ) * HLm Γ 5 L11662 + (-1 : ℝ) * HLm Γ 5 L11664 := by
  have h := HLm_submod hΓ [F0] L11665 [F217]
  rw [show [F0] ++ L11665 ++ [F217] = L11663 from rfl, show [F0] ++ L11665 = L11659 from rfl,
    show L11665 ++ [F217] = L11661 from rfl] at h
  rw [i7126 hinj, i7124 hinj, i7125 hinj, i7127 hinj] at h
  linarith

theorem row2391 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3529 + (1 : ℝ) * HLm Γ 5 L11628 + (-1 : ℝ) * HLm Γ 5 L11624 + (-1 : ℝ) * HLm Γ 5 L2305 := by
  have h := HLm_submod hΓ [F210] L2305 [F86]
  rw [show [F210] ++ L2305 ++ [F86] = L11667 from rfl, show [F210] ++ L2305 = L11666 from rfl,
    show L2305 ++ [F86] = L11629 from rfl] at h
  rw [i7129 hinj, i7128 hinj, i7107 hinj] at h
  linarith

theorem row2392 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L11669 + (-1 : ℝ) * HLm Γ 5 L4558 + (-1 : ℝ) * HLm Γ 5 L11672 := by
  have h := HLm_submod hΓ [F0] L11673 [F218]
  rw [show [F0] ++ L11673 ++ [F218] = L11671 from rfl, show [F0] ++ L11673 = L11668 from rfl,
    show L11673 ++ [F218] = L11670 from rfl] at h
  rw [i7132 hinj, i7130 hinj, i7131 hinj, i7133 hinj] at h
  linarith

theorem row2393 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11674 + (1 : ℝ) * HLm Γ 5 L11676 + (-1 : ℝ) * HLm Γ 5 L11678 + (-1 : ℝ) * HLm Γ 5 L11680 := by
  have h := HLm_submod hΓ [F1] L11681 [F210]
  rw [show [F1] ++ L11681 ++ [F210] = L11679 from rfl, show [F1] ++ L11681 = L11675 from rfl,
    show L11681 ++ [F210] = L11677 from rfl] at h
  rw [i7136 hinj, i7134 hinj, i7135 hinj, i7137 hinj] at h
  linarith

theorem row2394 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3867 + (1 : ℝ) * HLm Γ 5 L11487 + (-1 : ℝ) * HLm Γ 5 L11484 + (-1 : ℝ) * HLm Γ 5 L3865 := by
  have h := HLm_submod hΓ [F228] L3866 [F29]
  rw [show [F228] ++ L3866 ++ [F29] = L11682 from rfl, show [F228] ++ L3866 = L3868 from rfl,
    show L3866 ++ [F29] = L11488 from rfl] at h
  rw [i7138 hinj, i2160 hinj, i7026 hinj, i2159 hinj] at h
  linarith

theorem row2395 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11632 + (1 : ℝ) * HLm Γ 5 L11597 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L11595 := by
  have h := HLm_submod hΓ [F47] L11686 [F16]
  rw [show [F47] ++ L11686 ++ [F16] = L11685 from rfl, show [F47] ++ L11686 = L11683 from rfl,
    show L11686 ++ [F16] = L11684 from rfl] at h
  rw [i7141 hinj, i7139 hinj, i7140 hinj, i7142 hinj] at h
  linarith

theorem row2396 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11687 + (1 : ℝ) * HLm Γ 5 L11689 + (-1 : ℝ) * HLm Γ 5 L11691 + (-1 : ℝ) * HLm Γ 5 L11693 := by
  have h := HLm_submod hΓ [F107] L11694 [F217]
  rw [show [F107] ++ L11694 ++ [F217] = L11692 from rfl, show [F107] ++ L11694 = L11688 from rfl,
    show L11694 ++ [F217] = L11690 from rfl] at h
  rw [i7145 hinj, i7143 hinj, i7144 hinj, i7146 hinj] at h
  linarith

theorem row2397 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9719 + (1 : ℝ) * HLm Γ 5 L11654 + (-1 : ℝ) * HLm Γ 5 L4252 + (-1 : ℝ) * HLm Γ 5 L11652 := by
  have h := HLm_submod hΓ [F0] L11698 [F1]
  rw [show [F0] ++ L11698 ++ [F1] = L11697 from rfl, show [F0] ++ L11698 = L11695 from rfl,
    show L11698 ++ [F1] = L11696 from rfl] at h
  rw [i7149 hinj, i7147 hinj, i7148 hinj, i7150 hinj] at h
  linarith

theorem row2398 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11699 + (1 : ℝ) * HLm Γ 5 L11701 + (-1 : ℝ) * HLm Γ 5 L11703 + (-1 : ℝ) * HLm Γ 5 L11705 := by
  have h := HLm_submod hΓ [F0] L11706 [F67]
  rw [show [F0] ++ L11706 ++ [F67] = L11704 from rfl, show [F0] ++ L11706 = L11700 from rfl,
    show L11706 ++ [F67] = L11702 from rfl] at h
  rw [i7153 hinj, i7151 hinj, i7152 hinj, i7154 hinj] at h
  linarith

theorem row2399 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11707 + (1 : ℝ) * HLm Γ 5 L11493 + (-1 : ℝ) * HLm Γ 5 L11490 + (-1 : ℝ) * HLm Γ 5 L11711 := by
  have h := HLm_submod hΓ [F210] L11712 [F55]
  rw [show [F210] ++ L11712 ++ [F55] = L11710 from rfl, show [F210] ++ L11712 = L11708 from rfl,
    show L11712 ++ [F55] = L11709 from rfl] at h
  rw [i7157 hinj, i7155 hinj, i7156 hinj, i7158 hinj] at h
  linarith

end EntropyBounds.TwoSet.Certs.R7A5
