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

theorem row2850 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L204 + (-1 : ℝ) * HLm (mirror Γ) 5 L147 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 1, 2, 3, 4] ![0, 1, 2, 3, 4] (by decide) L147 L11847 (by decide)
  rw [i7277 hinj] at h
  linarith

theorem row2851 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L204 + (-1 : ℝ) * HLm (mirror Γ) 5 L427 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L428 L204 (by decide)
  rw [i174 hinj'] at h
  linarith

theorem row2852 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L204 + (-1 : ℝ) * HLm (mirror Γ) 5 L1955 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![2, 0, 1, 3, 4] ![1, 2, 0, 3, 4] (by decide) L1956 L204 (by decide)
  rw [i1079 hinj'] at h
  linarith

theorem row2853 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L204 + (-1 : ℝ) * HLm (mirror Γ) 5 L461 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![2, 3, 0, 1, 4] ![2, 3, 0, 1, 4] (by decide) L461 L11847 (by decide)
  rw [i7277 hinj] at h
  linarith

theorem row2854 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L205 + (-1 : ℝ) * HLm (mirror Γ) 5 L205 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 1, 2, 3, 4] ![0, 1, 2, 3, 4] (by decide) L205 L11848 (by decide)
  rw [i7278 hinj] at h
  linarith

theorem row2855 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L206 + (-1 : ℝ) * HLm (mirror Γ) 5 L1167 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![2, 3, 0, 1, 4] ![2, 3, 0, 1, 4] (by decide) L1168 L11849 (by decide)
  rw [i559 hinj', i7279 hinj] at h
  linarith

theorem row2856 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L210 + (-1 : ℝ) * HLm (mirror Γ) 5 L660 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![2, 0, 1, 3, 4] ![1, 2, 0, 3, 4] (by decide) L661 L11850 (by decide)
  rw [i286 hinj', i7280 hinj] at h
  linarith

theorem row2857 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L210 + (-1 : ℝ) * HLm Γ 5 L2952 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 4, 2] ![0, 1, 4, 2, 3] (by decide) L2952 L210 (by decide)
  linarith

theorem row2858 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L212 + (-1 : ℝ) * HLm Γ 5 L930 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L931 L213 (by decide)
  rw [i75 hinj, i428 hinj] at h
  linarith

theorem row2859 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L924 + (-1 : ℝ) * HLm Γ 5 L214 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L11852 L11851 (by decide)
  rw [i7281 hinj, i7282 hinj] at h
  linarith

theorem row2860 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L216 + (-1 : ℝ) * HLm (mirror Γ) 5 L3339 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![2, 0, 1, 3, 4] ![1, 2, 0, 3, 4] (by decide) L3339 L11853 (by decide)
  rw [i7283 hinj] at h
  linarith

theorem row2861 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L216 + (-1 : ℝ) * HLm (mirror Γ) 5 L11223 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![2, 0, 3, 1, 4] ![1, 3, 0, 2, 4] (by decide) L11223 L11853 (by decide)
  rw [i7283 hinj] at h
  linarith

theorem row2862 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L216 + (-1 : ℝ) * HLm (mirror Γ) 5 L7333 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![2, 3, 0, 1, 4] ![2, 3, 0, 1, 4] (by decide) L7333 L11853 (by decide)
  rw [i7283 hinj] at h
  linarith

theorem row2863 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L216 + (-1 : ℝ) * HLm (mirror Γ) 5 L349 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L2961 L11853 (by decide)
  rw [i1687 hinj', i7283 hinj] at h
  linarith

theorem row2864 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L216 + (-1 : ℝ) * HLm (mirror Γ) 5 L7364 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 2, 3, 4, 1] ![0, 4, 1, 2, 3] (by decide) L7365 L11853 (by decide)
  rw [i4363 hinj', i7283 hinj] at h
  linarith

theorem row2865 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L216 + (-1 : ℝ) * HLm Γ 5 L6897 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 4, 2] ![0, 1, 4, 2, 3] (by decide) L6897 L216 (by decide)
  linarith

theorem row2866 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2037 + (-1 : ℝ) * HLm Γ 5 L216 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L216 L2037 (by decide)
  linarith

theorem row2867 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L849 + (-1 : ℝ) * HLm Γ 5 L1960 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 3, 2, 1, 4] ![0, 3, 2, 1, 4] (by decide) L1961 L850 (by decide)
  rw [i386 hinj, i1081 hinj] at h
  linarith

theorem row2868 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L222 + (-1 : ℝ) * HLm Γ 5 L1960 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L1961 L223 (by decide)
  rw [i79 hinj, i1081 hinj] at h
  linarith

theorem row2869 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L7126 + (-1 : ℝ) * HLm Γ 5 L724 = 0 := by
  have h := HLm_permB (Γ := Γ) ![3, 1, 2, 0, 4] ![3, 1, 2, 0, 4] (by decide) L725 L7126 (by decide)
  rw [i317 hinj] at h
  linarith

theorem row2870 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11854 + (-1 : ℝ) * HLm Γ 5 L3021 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L3022 L11855 (by decide)
  rw [i7284 hinj, i1719 hinj] at h
  linarith

theorem row2871 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L224 + (-1 : ℝ) * HLm Γ 5 L965 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 3, 2, 1, 4] ![0, 3, 2, 1, 4] (by decide) L966 L11856 (by decide)
  rw [i7285 hinj, i446 hinj] at h
  linarith

theorem row2872 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L7126 + (-1 : ℝ) * HLm Γ 5 L224 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L224 L7126 (by decide)
  linarith

theorem row2873 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3822 + (-1 : ℝ) * HLm Γ 5 L224 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L224 L3822 (by decide)
  linarith

theorem row2874 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11854 + (-1 : ℝ) * HLm Γ 5 L224 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L224 L11854 (by decide)
  linarith

theorem row2875 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L225 + (-1 : ℝ) * HLm Γ 5 L1637 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L11858 L11857 (by decide)
  rw [i7286 hinj, i7287 hinj] at h
  linarith

theorem row2876 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L225 + (-1 : ℝ) * HLm Γ 5 L2338 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L11859 L11857 (by decide)
  rw [i7286 hinj, i7288 hinj] at h
  linarith

theorem row2877 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11860 + (-1 : ℝ) * HLm Γ 5 L3650 = 0 := by
  have h := HLm_permB (Γ := Γ) ![2, 1, 0, 3, 4] ![2, 1, 0, 3, 4] (by decide) L3650 L11861 (by decide)
  rw [i7289 hinj] at h
  linarith

theorem row2878 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11862 + (-1 : ℝ) * HLm Γ 5 L3105 = 0 := by
  have h := HLm_permB (Γ := Γ) ![3, 1, 2, 0, 4] ![3, 1, 2, 0, 4] (by decide) L3105 L11862 (by decide)
  linarith

theorem row2879 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11863 + (-1 : ℝ) * HLm Γ 5 L3643 = 0 := by
  have h := HLm_permB (Γ := Γ) ![3, 1, 2, 0, 4] ![3, 1, 2, 0, 4] (by decide) L3643 L11864 (by decide)
  rw [i7290 hinj] at h
  linarith

theorem row2880 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11865 + (-1 : ℝ) * HLm Γ 5 L717 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 3, 2, 1, 4] ![0, 3, 2, 1, 4] (by decide) L717 L11865 (by decide)
  linarith

theorem row2881 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L227 + (-1 : ℝ) * HLm Γ 5 L11860 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 4, 2] ![1, 0, 4, 2, 3] (by decide) L11861 L228 (by decide)
  rw [i81 hinj, i7289 hinj] at h
  linarith

theorem row2882 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3945 + (-1 : ℝ) * HLm Γ 5 L227 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 4, 2] ![1, 0, 4, 2, 3] (by decide) L227 L3945 (by decide)
  linarith

theorem row2883 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11862 + (-1 : ℝ) * HLm Γ 5 L227 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L227 L11862 (by decide)
  linarith

theorem row2884 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11863 + (-1 : ℝ) * HLm Γ 5 L227 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L227 L11863 (by decide)
  linarith

theorem row2885 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2992 + (-1 : ℝ) * HLm Γ 5 L227 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 4, 2] ![0, 1, 4, 2, 3] (by decide) L227 L2992 (by decide)
  linarith

theorem row2886 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11865 + (-1 : ℝ) * HLm Γ 5 L227 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L227 L11865 (by decide)
  linarith

theorem row2887 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L233 + (-1 : ℝ) * HLm (mirror Γ) 5 L178 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L179 L11866 (by decide)
  rw [i61 hinj', i7291 hinj] at h
  linarith

theorem row2888 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L233 + (-1 : ℝ) * HLm Γ 5 L252 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L252 L233 (by decide)
  linarith

theorem row2889 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3245 + (-1 : ℝ) * HLm Γ 5 L233 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L233 L3245 (by decide)
  linarith

theorem row2890 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11649 + (-1 : ℝ) * HLm Γ 5 L235 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L8153 L11650 (by decide)
  rw [i7119 hinj, i4809 hinj] at h
  linarith

theorem row2891 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L235 + (-1 : ℝ) * HLm Γ 5 L3224 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 4, 2] ![0, 1, 4, 2, 3] (by decide) L4237 L8153 (by decide)
  rw [i4809 hinj, i2368 hinj] at h
  linarith

theorem row2892 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3427 + (-1 : ℝ) * HLm Γ 5 L239 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L11868 L11867 (by decide)
  rw [i7292 hinj, i7293 hinj] at h
  linarith

theorem row2893 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L947 + (-1 : ℝ) * HLm Γ 5 L239 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L11868 L11869 (by decide)
  rw [i7294 hinj, i7293 hinj] at h
  linarith

theorem row2894 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L247 + (-1 : ℝ) * HLm (mirror Γ) 5 L878 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L878 L11870 (by decide)
  rw [i7295 hinj] at h
  linarith

theorem row2895 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2085 + (-1 : ℝ) * HLm Γ 5 L247 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L371 L2183 (by decide)
  rw [i1197 hinj, i148 hinj] at h
  linarith

theorem row2896 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L891 + (-1 : ℝ) * HLm Γ 5 L256 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L1271 L892 (by decide)
  rw [i406 hinj, i622 hinj] at h
  linarith

theorem row2897 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L845 + (-1 : ℝ) * HLm Γ 5 L260 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 3, 2, 1, 4] ![0, 3, 2, 1, 4] (by decide) L11872 L11871 (by decide)
  rw [i7296 hinj, i7297 hinj] at h
  linarith

theorem row2898 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L260 + (-1 : ℝ) * HLm Γ 5 L1276 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L11873 L11872 (by decide)
  rw [i7297 hinj, i7298 hinj] at h
  linarith

theorem row2899 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L1033 + (-1 : ℝ) * HLm Γ 5 L263 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 3, 2, 1, 4] ![0, 3, 2, 1, 4] (by decide) L11875 L11874 (by decide)
  rw [i7299 hinj, i7300 hinj] at h
  linarith

theorem row2900 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3859 + (-1 : ℝ) * HLm Γ 5 L263 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L11875 L11876 (by decide)
  rw [i7301 hinj, i7300 hinj] at h
  linarith

theorem row2901 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L265 + (-1 : ℝ) * HLm (mirror Γ) 5 L288 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L288 L11877 (by decide)
  rw [i7302 hinj] at h
  linarith

theorem row2902 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L276 + (-1 : ℝ) * HLm (mirror Γ) 5 L2362 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L2362 L11878 (by decide)
  rw [i7303 hinj] at h
  linarith

theorem row2903 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L1230 + (-1 : ℝ) * HLm Γ 5 L278 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L11880 L11879 (by decide)
  rw [i7304 hinj, i7305 hinj] at h
  linarith

theorem row2904 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L282 + (-1 : ℝ) * HLm Γ 5 L776 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L2660 L11881 (by decide)
  rw [i7306 hinj, i1494 hinj] at h
  linarith

theorem row2905 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L284 + (-1 : ℝ) * HLm Γ 5 L1009 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L1010 L11882 (by decide)
  rw [i7307 hinj, i470 hinj] at h
  linarith

theorem row2906 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L288 + (-1 : ℝ) * HLm (mirror Γ) 5 L265 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L266 L11883 (by decide)
  rw [i99 hinj', i7308 hinj] at h
  linarith

theorem row2907 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L288 + (-1 : ℝ) * HLm (mirror Γ) 5 L1988 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 1, 2, 3, 4] ![0, 1, 2, 3, 4] (by decide) L1989 L11884 (by decide)
  rw [i1091 hinj', i7309 hinj] at h
  linarith

theorem row2908 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L295 + (-1 : ℝ) * HLm Γ 5 L3851 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 4, 2] ![0, 1, 4, 2, 3] (by decide) L3852 L11885 (by decide)
  rw [i7310 hinj, i2152 hinj] at h
  linarith

theorem row2909 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11886 + (-1 : ℝ) * HLm Γ 5 L3256 = 0 := by
  have h := HLm_permB (Γ := Γ) ![3, 1, 2, 0, 4] ![3, 1, 2, 0, 4] (by decide) L3257 L11887 (by decide)
  rw [i7311 hinj, i1837 hinj] at h
  linarith

theorem row2910 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11886 + (-1 : ℝ) * HLm Γ 5 L320 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L6990 L11888 (by decide)
  rw [i7312 hinj, i4152 hinj] at h
  linarith

theorem row2911 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L952 + (-1 : ℝ) * HLm Γ 5 L11889 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L11890 L953 (by decide)
  rw [i440 hinj, i7313 hinj] at h
  linarith

theorem row2912 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L320 + (-1 : ℝ) * HLm Γ 5 L297 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 3, 2, 1, 4] ![0, 3, 2, 1, 4] (by decide) L298 L6990 (by decide)
  rw [i4152 hinj, i114 hinj] at h
  linarith

theorem row2913 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11889 + (-1 : ℝ) * HLm Γ 5 L297 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L298 L11890 (by decide)
  rw [i7313 hinj, i114 hinj] at h
  linarith

theorem row2914 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11891 + (-1 : ℝ) * HLm Γ 5 L3417 = 0 := by
  have h := HLm_permB (Γ := Γ) ![2, 1, 0, 3, 4] ![2, 1, 0, 3, 4] (by decide) L3418 L11892 (by decide)
  rw [i7314 hinj, i1918 hinj] at h
  linarith

theorem row2915 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L303 + (-1 : ℝ) * HLm (mirror Γ) 5 L94 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L94 L11893 (by decide)
  rw [i7315 hinj] at h
  linarith

theorem row2916 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L303 + (-1 : ℝ) * HLm Γ 5 L3425 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 4, 2] ![1, 0, 4, 2, 3] (by decide) L3426 L635 (by decide)
  rw [i273 hinj, i1922 hinj] at h
  linarith

theorem row2917 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11891 + (-1 : ℝ) * HLm Γ 5 L303 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L635 L11892 (by decide)
  rw [i7314 hinj, i273 hinj] at h
  linarith

theorem row2918 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2866 + (-1 : ℝ) * HLm Γ 5 L303 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L635 L7280 (by decide)
  rw [i4317 hinj, i273 hinj] at h
  linarith

theorem row2919 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3361 + (-1 : ℝ) * HLm Γ 5 L305 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 4, 3, 2] ![0, 1, 4, 3, 2] (by decide) L2050 L11894 (by decide)
  rw [i7316 hinj, i1124 hinj] at h
  linarith

theorem row2920 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L305 + (-1 : ℝ) * HLm Γ 5 L3346 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 4, 2] ![0, 1, 4, 2, 3] (by decide) L3347 L11895 (by decide)
  rw [i7317 hinj, i1883 hinj] at h
  linarith

theorem row2921 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3354 + (-1 : ℝ) * HLm Γ 5 L305 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L2050 L11896 (by decide)
  rw [i7318 hinj, i1124 hinj] at h
  linarith

theorem row2922 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L309 + (-1 : ℝ) * HLm Γ 5 L979 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L980 L11897 (by decide)
  rw [i7319 hinj, i454 hinj] at h
  linarith

theorem row2923 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3687 + (-1 : ℝ) * HLm Γ 5 L11898 = 0 := by
  have h := HLm_permB (Γ := Γ) ![4, 1, 2, 3, 0] ![4, 1, 2, 3, 0] (by decide) L11899 L3687 (by decide)
  rw [i7320 hinj] at h
  linarith

theorem row2924 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11898 + (-1 : ℝ) * HLm Γ 5 L468 = 0 := by
  have h := HLm_permB (Γ := Γ) ![2, 1, 0, 3, 4] ![2, 1, 0, 3, 4] (by decide) L468 L11900 (by decide)
  rw [i7321 hinj] at h
  linarith

theorem row2925 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3792 + (-1 : ℝ) * HLm Γ 5 L310 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 4, 2, 3, 1] ![0, 4, 2, 3, 1] (by decide) L11901 L3792 (by decide)
  rw [i7322 hinj] at h
  linarith

theorem row2926 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3110 + (-1 : ℝ) * HLm Γ 5 L310 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L11901 L11902 (by decide)
  rw [i7323 hinj, i7322 hinj] at h
  linarith

theorem row2927 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11898 + (-1 : ℝ) * HLm Γ 5 L310 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L11901 L11899 (by decide)
  rw [i7320 hinj, i7322 hinj] at h
  linarith

theorem row2928 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L310 + (-1 : ℝ) * HLm Γ 5 L3529 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 4, 2] ![0, 1, 4, 2, 3] (by decide) L3529 L310 (by decide)
  linarith

theorem row2929 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2314 + (-1 : ℝ) * HLm Γ 5 L310 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L11901 L11903 (by decide)
  rw [i7324 hinj, i7322 hinj] at h
  linarith

theorem row2930 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L314 + (-1 : ℝ) * HLm Γ 5 L3814 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 3, 2, 1, 4] ![0, 3, 2, 1, 4] (by decide) L3815 L11904 (by decide)
  rw [i7325 hinj, i2132 hinj] at h
  linarith

theorem row2931 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L316 + (-1 : ℝ) * HLm Γ 5 L3592 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L4157 L11905 (by decide)
  rw [i7326 hinj, i2321 hinj] at h
  linarith

theorem row2932 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L318 + (-1 : ℝ) * HLm (mirror Γ) 5 L2143 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L11907 L11906 (by decide)
  rw [i7328 hinj', i7327 hinj] at h
  linarith

theorem row2933 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L321 + (-1 : ℝ) * HLm Γ 5 L934 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L11909 L11908 (by decide)
  rw [i7329 hinj, i7330 hinj] at h
  linarith

theorem row2934 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L1202 + (-1 : ℝ) * HLm Γ 5 L330 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L3881 L11910 (by decide)
  rw [i7331 hinj, i2167 hinj] at h
  linarith

theorem row2935 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L726 + (-1 : ℝ) * HLm Γ 5 L335 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L11912 L11911 (by decide)
  rw [i7332 hinj, i7333 hinj] at h
  linarith

theorem row2936 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L335 + (-1 : ℝ) * HLm Γ 5 L572 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L572 L11912 (by decide)
  rw [i7333 hinj] at h
  linarith

theorem row2937 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L1047 + (-1 : ℝ) * HLm Γ 5 L342 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L11913 L1048 (by decide)
  rw [i490 hinj, i7334 hinj] at h
  linarith

theorem row2938 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3303 + (-1 : ℝ) * HLm Γ 5 L344 = 0 := by
  have h := HLm_permB (Γ := Γ) ![3, 1, 2, 0, 4] ![3, 1, 2, 0, 4] (by decide) L345 L3303 (by decide)
  rw [i136 hinj] at h
  linarith

theorem row2939 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L344 + (-1 : ℝ) * HLm Γ 5 L544 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L544 L345 (by decide)
  rw [i136 hinj] at h
  linarith

theorem row2940 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L347 + (-1 : ℝ) * HLm Γ 5 L602 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L603 L11914 (by decide)
  rw [i7335 hinj, i256 hinj] at h
  linarith

theorem row2941 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L349 + (-1 : ℝ) * HLm (mirror Γ) 5 L216 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L216 L11915 (by decide)
  rw [i7336 hinj] at h
  linarith

theorem row2942 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L349 + (-1 : ℝ) * HLm (mirror Γ) 5 L2037 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 2, 3, 1, 4] ![0, 3, 1, 2, 4] (by decide) L2037 L11915 (by decide)
  rw [i7336 hinj] at h
  linarith

theorem row2943 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L349 + (-1 : ℝ) * HLm (mirror Γ) 5 L6897 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 2, 3, 4, 1] ![0, 4, 1, 2, 3] (by decide) L6897 L11915 (by decide)
  rw [i7336 hinj] at h
  linarith

theorem row2944 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L349 + (-1 : ℝ) * HLm Γ 5 L11573 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 4, 2] ![1, 0, 4, 2, 3] (by decide) L11573 L2961 (by decide)
  rw [i1687 hinj] at h
  linarith

theorem row2945 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L349 + (-1 : ℝ) * HLm Γ 5 L3339 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L3339 L2961 (by decide)
  rw [i1687 hinj] at h
  linarith

theorem row2946 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L354 + (-1 : ℝ) * HLm Γ 5 L889 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L890 L11916 (by decide)
  rw [i7337 hinj, i405 hinj] at h
  linarith

theorem row2947 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L356 + (-1 : ℝ) * HLm Γ 5 L362 = 0 := by
  have h := HLm_permB (Γ := Γ) ![2, 1, 0, 3, 4] ![2, 1, 0, 3, 4] (by decide) L363 L3076 (by decide)
  rw [i1749 hinj, i144 hinj] at h
  linarith

theorem row2948 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L445 + (-1 : ℝ) * HLm Γ 5 L356 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L357 L446 (by decide)
  rw [i183 hinj, i141 hinj] at h
  linarith

theorem row2949 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11917 + (-1 : ℝ) * HLm Γ 5 L480 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 3, 2, 1, 4] ![0, 3, 2, 1, 4] (by decide) L481 L11918 (by decide)
  rw [i7338 hinj, i200 hinj] at h
  linarith

theorem row2950 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3179 + (-1 : ℝ) * HLm Γ 5 L360 = 0 := by
  have h := HLm_permB (Γ := Γ) ![3, 1, 2, 0, 4] ![3, 1, 2, 0, 4] (by decide) L2093 L11919 (by decide)
  rw [i7339 hinj, i1148 hinj] at h
  linarith

theorem row2951 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L360 + (-1 : ℝ) * HLm Γ 5 L11917 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L11918 L361 (by decide)
  rw [i143 hinj, i7338 hinj] at h
  linarith

theorem row2952 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L364 + (-1 : ℝ) * HLm Γ 5 L1635 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L1636 L11920 (by decide)
  rw [i7340 hinj, i842 hinj] at h
  linarith

theorem row2953 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L372 + (-1 : ℝ) * HLm Γ 5 L1081 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L11922 L11921 (by decide)
  rw [i7341 hinj, i7342 hinj] at h
  linarith

theorem row2954 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L384 + (-1 : ℝ) * HLm (mirror Γ) 5 L114 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![3, 2, 0, 1, 4] ![2, 3, 1, 0, 4] (by decide) L114 L11923 (by decide)
  rw [i7343 hinj] at h
  linarith

theorem row2955 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L384 + (-1 : ℝ) * HLm Γ 5 L509 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L11788 L2989 (by decide)
  rw [i1704 hinj, i7226 hinj] at h
  linarith

theorem row2956 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3093 + (-1 : ℝ) * HLm Γ 5 L384 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 2, 4, 3] ![0, 1, 2, 4, 3] (by decide) L2989 L11924 (by decide)
  rw [i7344 hinj, i1704 hinj] at h
  linarith

theorem row2957 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L387 + (-1 : ℝ) * HLm (mirror Γ) 5 L549 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![2, 0, 3, 1, 4] ![1, 3, 0, 2, 4] (by decide) L549 L11925 (by decide)
  rw [i7345 hinj] at h
  linarith

theorem row2958 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L387 + (-1 : ℝ) * HLm (mirror Γ) 5 L32 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![2, 3, 0, 1, 4] ![2, 3, 0, 1, 4] (by decide) L32 L11925 (by decide)
  rw [i7345 hinj] at h
  linarith

theorem row2959 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L387 + (-1 : ℝ) * HLm (mirror Γ) 5 L68 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L68 L11925 (by decide)
  rw [i7345 hinj] at h
  linarith

theorem row2960 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L387 + (-1 : ℝ) * HLm (mirror Γ) 5 L11237 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 2, 3, 1, 4] ![0, 3, 1, 2, 4] (by decide) L11237 L11925 (by decide)
  rw [i7345 hinj] at h
  linarith

theorem row2961 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L387 + (-1 : ℝ) * HLm (mirror Γ) 5 L13 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![3, 2, 0, 1, 4] ![2, 3, 1, 0, 4] (by decide) L13 L11925 (by decide)
  rw [i7345 hinj] at h
  linarith

theorem row2962 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11713 + (-1 : ℝ) * HLm Γ 5 L387 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L387 L11713 (by decide)
  linarith

theorem row2963 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3159 + (-1 : ℝ) * HLm Γ 5 L677 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L678 L3164 (by decide)
  rw [i1790 hinj, i294 hinj] at h
  linarith

theorem row2964 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3159 + (-1 : ℝ) * HLm Γ 5 L388 = 0 := by
  have h := HLm_permB (Γ := Γ) ![3, 1, 2, 0, 4] ![3, 1, 2, 0, 4] (by decide) L389 L11926 (by decide)
  rw [i7346 hinj, i156 hinj] at h
  linarith

theorem row2965 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L390 + (-1 : ℝ) * HLm Γ 5 L611 = 0 := by
  have h := HLm_permB (Γ := Γ) ![3, 1, 2, 0, 4] ![3, 1, 2, 0, 4] (by decide) L611 L2849 (by decide)
  rw [i1632 hinj] at h
  linarith

theorem row2966 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L391 + (-1 : ℝ) * HLm Γ 5 L3160 = 0 := by
  have h := HLm_permB (Γ := Γ) ![3, 1, 2, 0, 4] ![3, 1, 2, 0, 4] (by decide) L8139 L11927 (by decide)
  rw [i7347 hinj, i4799 hinj] at h
  linarith

theorem row2967 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L1236 + (-1 : ℝ) * HLm Γ 5 L404 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L6962 L11928 (by decide)
  rw [i7348 hinj, i4136 hinj] at h
  linarith

theorem row2968 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L991 + (-1 : ℝ) * HLm Γ 5 L2059 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 3, 2, 1, 4] ![0, 3, 2, 1, 4] (by decide) L2060 L11929 (by decide)
  rw [i7349 hinj, i1129 hinj] at h
  linarith

theorem row2969 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L421 + (-1 : ℝ) * HLm (mirror Γ) 5 L910 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L911 L11930 (by decide)
  rw [i418 hinj', i7350 hinj] at h
  linarith

theorem row2970 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L421 + (-1 : ℝ) * HLm (mirror Γ) 5 L3765 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 2, 3, 1, 4] ![0, 3, 1, 2, 4] (by decide) L3766 L11930 (by decide)
  rw [i2104 hinj', i7350 hinj] at h
  linarith

theorem row2971 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L457 + (-1 : ℝ) * HLm Γ 5 L421 = 0 := by
  have h := HLm_permB (Γ := Γ) ![3, 1, 2, 0, 4] ![3, 1, 2, 0, 4] (by decide) L872 L11931 (by decide)
  rw [i7351 hinj, i397 hinj] at h
  linarith

theorem row2972 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2059 + (-1 : ℝ) * HLm Γ 5 L421 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L872 L2060 (by decide)
  rw [i1129 hinj, i397 hinj] at h
  linarith

theorem row2973 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L4030 + (-1 : ℝ) * HLm Γ 5 L423 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L3982 L4031 (by decide)
  rw [i2249 hinj, i2222 hinj] at h
  linarith

theorem row2974 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L423 + (-1 : ℝ) * HLm Γ 5 L1039 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L1040 L3982 (by decide)
  rw [i2222 hinj, i486 hinj] at h
  linarith

theorem row2975 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L425 + (-1 : ℝ) * HLm Γ 5 L893 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L11933 L11932 (by decide)
  rw [i7352 hinj, i7353 hinj] at h
  linarith

theorem row2976 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L1622 + (-1 : ℝ) * HLm Γ 5 L2246 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 3, 2, 1, 4] ![0, 3, 2, 1, 4] (by decide) L11935 L11934 (by decide)
  rw [i7354 hinj, i7355 hinj] at h
  linarith

theorem row2977 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L433 + (-1 : ℝ) * HLm Γ 5 L2246 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L11935 L11936 (by decide)
  rw [i7356 hinj, i7355 hinj] at h
  linarith

theorem row2978 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L4038 + (-1 : ℝ) * HLm Γ 5 L435 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 4, 3] ![1, 0, 2, 4, 3] (by decide) L436 L4039 (by decide)
  rw [i2253 hinj, i178 hinj] at h
  linarith

theorem row2979 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L435 + (-1 : ℝ) * HLm Γ 5 L3937 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L3938 L436 (by decide)
  rw [i178 hinj, i2198 hinj] at h
  linarith

theorem row2980 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L437 + (-1 : ℝ) * HLm Γ 5 L975 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L11938 L11937 (by decide)
  rw [i7357 hinj, i7358 hinj] at h
  linarith

theorem row2981 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L4055 + (-1 : ℝ) * HLm Γ 5 L439 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 4, 3] ![1, 0, 2, 4, 3] (by decide) L440 L4056 (by decide)
  rw [i2263 hinj, i180 hinj] at h
  linarith

theorem row2982 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L439 + (-1 : ℝ) * HLm Γ 5 L3001 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L3002 L440 (by decide)
  rw [i180 hinj, i1710 hinj] at h
  linarith

theorem row2983 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3200 + (-1 : ℝ) * HLm Γ 5 L1113 = 0 := by
  have h := HLm_permB (Γ := Γ) ![3, 1, 2, 0, 4] ![3, 1, 2, 0, 4] (by decide) L1114 L3201 (by decide)
  rw [i1810 hinj, i528 hinj] at h
  linarith

theorem row2984 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L1113 + (-1 : ℝ) * HLm Γ 5 L3481 = 0 := by
  have h := HLm_permB (Γ := Γ) ![2, 1, 0, 3, 4] ![2, 1, 0, 3, 4] (by decide) L3482 L11939 (by decide)
  rw [i7359 hinj, i1953 hinj] at h
  linarith

theorem row2985 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L441 + (-1 : ℝ) * HLm Γ 5 L739 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L740 L11940 (by decide)
  rw [i7360 hinj, i325 hinj] at h
  linarith

theorem row2986 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L443 + (-1 : ℝ) * HLm Γ 5 L1109 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L11942 L11941 (by decide)
  rw [i7361 hinj, i7362 hinj] at h
  linarith

theorem row2987 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L447 + (-1 : ℝ) * HLm Γ 5 L1173 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L1174 L11943 (by decide)
  rw [i7363 hinj, i563 hinj] at h
  linarith

theorem row2988 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L449 + (-1 : ℝ) * HLm Γ 5 L1747 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L1748 L11944 (by decide)
  rw [i7364 hinj, i915 hinj] at h
  linarith

theorem row2989 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L459 + (-1 : ℝ) * HLm (mirror Γ) 5 L3753 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![2, 3, 1, 0, 4] ![3, 2, 0, 1, 4] (by decide) L11946 L11945 (by decide)
  rw [i7366 hinj', i7365 hinj] at h
  linarith

theorem row2990 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3350 + (-1 : ℝ) * HLm Γ 5 L459 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 2, 4, 3] ![0, 1, 2, 4, 3] (by decide) L11947 L3351 (by decide)
  rw [i1885 hinj, i7367 hinj] at h
  linarith

theorem row2991 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L462 + (-1 : ℝ) * HLm (mirror Γ) 5 L930 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![2, 3, 1, 0, 4] ![3, 2, 0, 1, 4] (by decide) L931 L11948 (by decide)
  rw [i428 hinj', i7368 hinj] at h
  linarith

theorem row2992 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L462 + (-1 : ℝ) * HLm Γ 5 L1221 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L1222 L463 (by decide)
  rw [i191 hinj, i590 hinj] at h
  linarith

theorem row2993 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L464 + (-1 : ℝ) * HLm (mirror Γ) 5 L924 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![2, 3, 1, 0, 4] ![3, 2, 0, 1, 4] (by decide) L11851 L11949 (by decide)
  rw [i7281 hinj', i7369 hinj] at h
  linarith

theorem row2994 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L1217 + (-1 : ℝ) * HLm Γ 5 L464 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L465 L11950 (by decide)
  rw [i7370 hinj, i192 hinj] at h
  linarith

theorem row2995 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L467 + (-1 : ℝ) * HLm Γ 5 L526 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L526 L11296 (by decide)
  rw [i6917 hinj] at h
  linarith

theorem row2996 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11164 + (-1 : ℝ) * HLm Γ 5 L472 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 4, 3, 2] ![1, 0, 4, 3, 2] (by decide) L11952 L11951 (by decide)
  rw [i7371 hinj, i7372 hinj] at h
  linarith

theorem row2997 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L478 + (-1 : ℝ) * HLm Γ 5 L1223 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L11953 L479 (by decide)
  rw [i199 hinj, i7373 hinj] at h
  linarith

theorem row2998 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L482 + (-1 : ℝ) * HLm Γ 5 L827 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L827 L11954 (by decide)
  rw [i7374 hinj] at h
  linarith

theorem row2999 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L1180 + (-1 : ℝ) * HLm Γ 5 L487 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L11956 L11955 (by decide)
  rw [i7375 hinj, i7376 hinj] at h
  linarith

end EntropyBounds.TwoSet.Certs.R7A5
