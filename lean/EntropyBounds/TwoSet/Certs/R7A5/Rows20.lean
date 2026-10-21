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

theorem row3000 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L862 + (-1 : ℝ) * HLm Γ 5 L487 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L11956 L11957 (by decide)
  rw [i7377 hinj, i7376 hinj] at h
  linarith

theorem row3001 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L493 + (-1 : ℝ) * HLm Γ 5 L883 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L3888 L11958 (by decide)
  rw [i7378 hinj, i2172 hinj] at h
  linarith

theorem row3002 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L495 + (-1 : ℝ) * HLm Γ 5 L833 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L834 L496 (by decide)
  rw [i207 hinj, i376 hinj] at h
  linarith

theorem row3003 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L498 + (-1 : ℝ) * HLm Γ 5 L829 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L11960 L11959 (by decide)
  rw [i7379 hinj, i7380 hinj] at h
  linarith

theorem row3004 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L501 + (-1 : ℝ) * HLm Γ 5 L504 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L505 L11961 (by decide)
  rw [i7381 hinj, i209 hinj] at h
  linarith

theorem row3005 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L836 + (-1 : ℝ) * HLm Γ 5 L502 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L11963 L11962 (by decide)
  rw [i7382 hinj, i7383 hinj] at h
  linarith

theorem row3006 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L503 + (-1 : ℝ) * HLm (mirror Γ) 5 L503 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![2, 3, 0, 1, 4] ![2, 3, 0, 1, 4] (by decide) L503 L11964 (by decide)
  rw [i7384 hinj] at h
  linarith

theorem row3007 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L875 + (-1 : ℝ) * HLm Γ 5 L511 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L11966 L11965 (by decide)
  rw [i7385 hinj, i7386 hinj] at h
  linarith

theorem row3008 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L516 + (-1 : ℝ) * HLm (mirror Γ) 5 L516 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![2, 3, 0, 1, 4] ![2, 3, 0, 1, 4] (by decide) L907 L11967 (by decide)
  rw [i416 hinj', i7387 hinj] at h
  linarith

theorem row3009 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L516 + (-1 : ℝ) * HLm (mirror Γ) 5 L9181 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![2, 3, 4, 0, 1] ![3, 4, 0, 1, 2] (by decide) L9182 L11967 (by decide)
  rw [i5426 hinj', i7387 hinj] at h
  linarith

theorem row3010 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3755 + (-1 : ℝ) * HLm Γ 5 L516 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 2, 4, 3] ![0, 1, 2, 4, 3] (by decide) L907 L3756 (by decide)
  rw [i2099 hinj, i416 hinj] at h
  linarith

theorem row3011 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L519 + (-1 : ℝ) * HLm Γ 5 L3840 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 4, 2] ![1, 0, 4, 2, 3] (by decide) L11969 L11968 (by decide)
  rw [i7388 hinj, i7389 hinj] at h
  linarith

theorem row3012 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L519 + (-1 : ℝ) * HLm Γ 5 L1053 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L5172 L11968 (by decide)
  rw [i7388 hinj, i2913 hinj] at h
  linarith

theorem row3013 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2858 + (-1 : ℝ) * HLm Γ 5 L11970 = 0 := by
  have h := HLm_permB (Γ := Γ) ![4, 1, 2, 3, 0] ![4, 1, 2, 3, 0] (by decide) L11971 L2858 (by decide)
  rw [i7390 hinj] at h
  linarith

theorem row3014 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11970 + (-1 : ℝ) * HLm Γ 5 L521 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L521 L11971 (by decide)
  rw [i7390 hinj] at h
  linarith

theorem row3015 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L681 + (-1 : ℝ) * HLm Γ 5 L524 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L11973 L11972 (by decide)
  rw [i7391 hinj, i7392 hinj] at h
  linarith

theorem row3016 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L534 + (-1 : ℝ) * HLm Γ 5 L1200 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L1201 L11974 (by decide)
  rw [i7393 hinj, i579 hinj] at h
  linarith

theorem row3017 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L542 + (-1 : ℝ) * HLm Γ 5 L1152 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L11976 L11975 (by decide)
  rw [i7394 hinj, i7395 hinj] at h
  linarith

theorem row3018 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3939 + (-1 : ℝ) * HLm Γ 5 L11977 = 0 := by
  have h := HLm_permB (Γ := Γ) ![4, 1, 0, 3, 2] ![2, 1, 4, 3, 0] (by decide) L11978 L3939 (by decide)
  rw [i7396 hinj] at h
  linarith

theorem row3019 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3236 + (-1 : ℝ) * HLm Γ 5 L552 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L552 L3236 (by decide)
  linarith

theorem row3020 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L954 + (-1 : ℝ) * HLm Γ 5 L550 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 3, 2, 1, 4] ![0, 3, 2, 1, 4] (by decide) L550 L954 (by decide)
  linarith

theorem row3021 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L550 + (-1 : ℝ) * HLm Γ 5 L2286 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L11980 L11979 (by decide)
  rw [i7397 hinj, i7398 hinj] at h
  linarith

theorem row3022 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11977 + (-1 : ℝ) * HLm Γ 5 L550 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L550 L11978 (by decide)
  rw [i7396 hinj] at h
  linarith

theorem row3023 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L552 + (-1 : ℝ) * HLm Γ 5 L550 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L550 L552 (by decide)
  linarith

theorem row3024 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L5148 + (-1 : ℝ) * HLm Γ 5 L11981 = 0 := by
  have h := HLm_permB (Γ := Γ) ![3, 1, 2, 0, 4] ![3, 1, 2, 0, 4] (by decide) L11982 L5148 (by decide)
  rw [i7399 hinj] at h
  linarith

theorem row3025 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L5228 + (-1 : ℝ) * HLm Γ 5 L11983 = 0 := by
  have h := HLm_permB (Γ := Γ) ![4, 1, 2, 3, 0] ![4, 1, 2, 3, 0] (by decide) L11984 L5228 (by decide)
  rw [i7400 hinj] at h
  linarith

theorem row3026 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11981 + (-1 : ℝ) * HLm Γ 5 L553 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 4, 3] ![1, 0, 2, 4, 3] (by decide) L553 L11982 (by decide)
  rw [i7399 hinj] at h
  linarith

theorem row3027 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11983 + (-1 : ℝ) * HLm Γ 5 L553 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L553 L11984 (by decide)
  rw [i7400 hinj] at h
  linarith

theorem row3028 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L5236 + (-1 : ℝ) * HLm Γ 5 L553 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 4, 2] ![0, 1, 4, 2, 3] (by decide) L553 L5236 (by decide)
  linarith

theorem row3029 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L557 + (-1 : ℝ) * HLm (mirror Γ) 5 L7624 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L11986 L11985 (by decide)
  rw [i7402 hinj', i7401 hinj] at h
  linarith

theorem row3030 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L557 + (-1 : ℝ) * HLm (mirror Γ) 5 L4374 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 2, 3, 1, 4] ![0, 3, 1, 2, 4] (by decide) L4375 L11985 (by decide)
  rw [i2452 hinj', i7401 hinj] at h
  linarith

theorem row3031 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L565 + (-1 : ℝ) * HLm (mirror Γ) 5 L897 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 1, 2, 3, 4] ![0, 1, 2, 3, 4] (by decide) L1359 L11987 (by decide)
  rw [i676 hinj', i7403 hinj] at h
  linarith

theorem row3032 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L673 + (-1 : ℝ) * HLm Γ 5 L11989 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L11990 L11988 (by decide)
  rw [i7404 hinj, i7405 hinj] at h
  linarith

theorem row3033 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L629 + (-1 : ℝ) * HLm Γ 5 L2090 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 3, 2, 1, 4] ![0, 3, 2, 1, 4] (by decide) L11991 L630 (by decide)
  rw [i270 hinj, i7406 hinj] at h
  linarith

theorem row3034 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3411 + (-1 : ℝ) * HLm Γ 5 L570 = 0 := by
  have h := HLm_permB (Γ := Γ) ![2, 1, 0, 3, 4] ![2, 1, 0, 3, 4] (by decide) L11992 L3412 (by decide)
  rw [i1915 hinj, i7407 hinj] at h
  linarith

theorem row3035 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11989 + (-1 : ℝ) * HLm Γ 5 L570 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L11992 L11990 (by decide)
  rw [i7405 hinj, i7407 hinj] at h
  linarith

theorem row3036 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2090 + (-1 : ℝ) * HLm Γ 5 L570 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L11992 L11991 (by decide)
  rw [i7406 hinj, i7407 hinj] at h
  linarith

theorem row3037 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L1385 + (-1 : ℝ) * HLm Γ 5 L9071 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L11994 L11993 (by decide)
  rw [i7408 hinj, i7409 hinj] at h
  linarith

theorem row3038 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3342 + (-1 : ℝ) * HLm Γ 5 L573 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L11996 L11995 (by decide)
  rw [i7410 hinj, i7411 hinj] at h
  linarith

theorem row3039 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L9071 + (-1 : ℝ) * HLm Γ 5 L573 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L11996 L11994 (by decide)
  rw [i7409 hinj, i7411 hinj] at h
  linarith

theorem row3040 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L578 + (-1 : ℝ) * HLm Γ 5 L1616 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L11997 L6882 (by decide)
  rw [i4094 hinj, i7412 hinj] at h
  linarith

theorem row3041 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L578 + (-1 : ℝ) * HLm Γ 5 L4412 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 4, 2] ![0, 1, 4, 2, 3] (by decide) L11999 L11998 (by decide)
  rw [i7413 hinj, i7414 hinj] at h
  linarith

theorem row3042 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L4791 + (-1 : ℝ) * HLm Γ 5 L1630 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 2, 4, 3] ![0, 1, 2, 4, 3] (by decide) L9022 L12000 (by decide)
  rw [i7415 hinj, i5328 hinj] at h
  linarith

theorem row3043 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L588 + (-1 : ℝ) * HLm Γ 5 L1630 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 3, 2, 1, 4] ![0, 3, 2, 1, 4] (by decide) L9022 L12001 (by decide)
  rw [i7416 hinj, i5328 hinj] at h
  linarith

theorem row3044 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L4138 + (-1 : ℝ) * HLm Γ 5 L588 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L12003 L12002 (by decide)
  rw [i7417 hinj, i7418 hinj] at h
  linarith

theorem row3045 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3143 + (-1 : ℝ) * HLm Γ 5 L588 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L12003 L12004 (by decide)
  rw [i7419 hinj, i7418 hinj] at h
  linarith

theorem row3046 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L1576 + (-1 : ℝ) * HLm Γ 5 L592 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L12006 L12005 (by decide)
  rw [i7420 hinj, i7421 hinj] at h
  linarith

theorem row3047 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L595 + (-1 : ℝ) * HLm Γ 5 L3444 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 3, 2, 1, 4] ![0, 3, 2, 1, 4] (by decide) L3444 L12007 (by decide)
  rw [i7422 hinj] at h
  linarith

theorem row3048 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L5110 + (-1 : ℝ) * HLm Γ 5 L595 = 0 := by
  have h := HLm_permB (Γ := Γ) ![4, 0, 2, 3, 1] ![1, 4, 2, 3, 0] (by decide) L595 L12008 (by decide)
  rw [i7423 hinj] at h
  linarith

theorem row3049 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L714 + (-1 : ℝ) * HLm Γ 5 L12010 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 3, 2, 1, 4] ![0, 3, 2, 1, 4] (by decide) L12011 L12009 (by decide)
  rw [i7424 hinj, i7425 hinj] at h
  linarith

theorem row3050 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3107 + (-1 : ℝ) * HLm Γ 5 L7174 = 0 := by
  have h := HLm_permB (Γ := Γ) ![3, 1, 2, 0, 4] ![3, 1, 2, 0, 4] (by decide) L7175 L12012 (by decide)
  rw [i7426 hinj, i4256 hinj] at h
  linarith

theorem row3051 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L4153 + (-1 : ℝ) * HLm Γ 5 L7174 = 0 := by
  have h := HLm_permB (Γ := Γ) ![2, 1, 0, 3, 4] ![2, 1, 0, 3, 4] (by decide) L7175 L12013 (by decide)
  rw [i7427 hinj, i4256 hinj] at h
  linarith

theorem row3052 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12010 + (-1 : ℝ) * HLm Γ 5 L607 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L607 L12014 (by decide)
  rw [i7428 hinj] at h
  linarith

theorem row3053 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L7174 + (-1 : ℝ) * HLm Γ 5 L607 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L607 L7174 (by decide)
  linarith

theorem row3054 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3248 + (-1 : ℝ) * HLm Γ 5 L609 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L12016 L12015 (by decide)
  rw [i7429 hinj, i7430 hinj] at h
  linarith

theorem row3055 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L619 + (-1 : ℝ) * HLm Γ 5 L3419 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 4, 2] ![1, 0, 4, 2, 3] (by decide) L12017 L620 (by decide)
  rw [i266 hinj, i7431 hinj] at h
  linarith

theorem row3056 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L619 + (-1 : ℝ) * HLm Γ 5 L4416 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 4, 2] ![0, 1, 4, 2, 3] (by decide) L4417 L620 (by decide)
  rw [i266 hinj, i2477 hinj] at h
  linarith

theorem row3057 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L1520 + (-1 : ℝ) * HLm Γ 5 L621 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L12019 L12018 (by decide)
  rw [i7432 hinj, i7433 hinj] at h
  linarith

theorem row3058 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L623 + (-1 : ℝ) * HLm (mirror Γ) 5 L2010 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L2011 L12020 (by decide)
  rw [i1101 hinj', i7434 hinj] at h
  linarith

theorem row3059 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L623 + (-1 : ℝ) * HLm (mirror Γ) 5 L307 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![1, 2, 0, 3, 4] ![2, 0, 1, 3, 4] (by decide) L307 L12021 (by decide)
  rw [i7435 hinj] at h
  linarith

theorem row3060 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L623 + (-1 : ℝ) * HLm (mirror Γ) 5 L6872 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![1, 2, 3, 4, 0] ![4, 0, 1, 2, 3] (by decide) L6872 L12021 (by decide)
  rw [i7435 hinj] at h
  linarith

theorem row3061 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L623 + (-1 : ℝ) * HLm (mirror Γ) 5 L6 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 1, 2, 3, 4] ![0, 1, 2, 3, 4] (by decide) L6 L12020 (by decide)
  rw [i7434 hinj] at h
  linarith

theorem row3062 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L636 + (-1 : ℝ) * HLm (mirror Γ) 5 L181 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![1, 2, 0, 3, 4] ![2, 0, 1, 3, 4] (by decide) L182 L12022 (by decide)
  rw [i62 hinj', i7436 hinj] at h
  linarith

theorem row3063 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L636 + (-1 : ℝ) * HLm (mirror Γ) 5 L7254 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![1, 2, 3, 0, 4] ![3, 0, 1, 2, 4] (by decide) L7255 L12022 (by decide)
  rw [i4300 hinj', i7436 hinj] at h
  linarith

theorem row3064 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L636 + (-1 : ℝ) * HLm Γ 5 L4219 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 4, 2] ![1, 0, 4, 2, 3] (by decide) L4220 L12023 (by decide)
  rw [i7437 hinj, i2358 hinj] at h
  linarith

theorem row3065 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L636 + (-1 : ℝ) * HLm Γ 5 L4212 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L4213 L12023 (by decide)
  rw [i7437 hinj, i2354 hinj] at h
  linarith

theorem row3066 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L642 + (-1 : ℝ) * HLm Γ 5 L1463 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L1464 L12024 (by decide)
  rw [i7438 hinj, i738 hinj] at h
  linarith

theorem row3067 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L1465 + (-1 : ℝ) * HLm Γ 5 L644 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L12026 L12025 (by decide)
  rw [i7439 hinj, i7440 hinj] at h
  linarith

theorem row3068 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L695 + (-1 : ℝ) * HLm Γ 5 L644 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L12026 L12027 (by decide)
  rw [i7441 hinj, i7440 hinj] at h
  linarith

theorem row3069 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L1458 + (-1 : ℝ) * HLm Γ 5 L644 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L12026 L12028 (by decide)
  rw [i7442 hinj, i7440 hinj] at h
  linarith

theorem row3070 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L648 + (-1 : ℝ) * HLm Γ 5 L1369 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L1370 L12029 (by decide)
  rw [i7443 hinj, i682 hinj] at h
  linarith

theorem row3071 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L652 + (-1 : ℝ) * HLm Γ 5 L1365 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L1366 L12030 (by decide)
  rw [i7444 hinj, i680 hinj] at h
  linarith

theorem row3072 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L654 + (-1 : ℝ) * HLm Γ 5 L4581 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 4, 2] ![1, 0, 4, 2, 3] (by decide) L4582 L8454 (by decide)
  rw [i4985 hinj, i2571 hinj] at h
  linarith

theorem row3073 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L765 + (-1 : ℝ) * HLm Γ 5 L654 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L8454 L12031 (by decide)
  rw [i7445 hinj, i4985 hinj] at h
  linarith

theorem row3074 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L656 + (-1 : ℝ) * HLm Γ 5 L1389 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 3, 2, 1, 4] ![0, 3, 2, 1, 4] (by decide) L1390 L7831 (by decide)
  rw [i4623 hinj, i694 hinj] at h
  linarith

theorem row3075 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L4859 + (-1 : ℝ) * HLm Γ 5 L658 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L12033 L12032 (by decide)
  rw [i7446 hinj, i7447 hinj] at h
  linarith

theorem row3076 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L658 + (-1 : ℝ) * HLm Γ 5 L11618 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L12035 L12034 (by decide)
  rw [i7448 hinj, i7449 hinj] at h
  linarith

theorem row3077 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L4381 + (-1 : ℝ) * HLm Γ 5 L671 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L2560 L7340 (by decide)
  rw [i4348 hinj, i1427 hinj] at h
  linarith

theorem row3078 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L4368 + (-1 : ℝ) * HLm Γ 5 L675 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 4, 3, 2] ![0, 1, 4, 3, 2] (by decide) L12037 L12036 (by decide)
  rw [i7450 hinj, i7451 hinj] at h
  linarith

theorem row3079 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L1473 + (-1 : ℝ) * HLm Γ 5 L675 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L12037 L12038 (by decide)
  rw [i7452 hinj, i7451 hinj] at h
  linarith

theorem row3080 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12039 + (-1 : ℝ) * HLm Γ 5 L11554 = 0 := by
  have h := HLm_permB (Γ := Γ) ![4, 1, 2, 3, 0] ![4, 1, 2, 3, 0] (by decide) L11555 L12040 (by decide)
  rw [i7453 hinj, i7062 hinj] at h
  linarith

theorem row3081 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12041 + (-1 : ℝ) * HLm Γ 5 L3220 = 0 := by
  have h := HLm_permB (Γ := Γ) ![3, 1, 2, 0, 4] ![3, 1, 2, 0, 4] (by decide) L3221 L12042 (by decide)
  rw [i7454 hinj, i1820 hinj] at h
  linarith

theorem row3082 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3873 + (-1 : ℝ) * HLm Γ 5 L12044 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 4, 1, 3, 2] ![0, 2, 4, 3, 1] (by decide) L12045 L12043 (by decide)
  rw [i7455 hinj, i7456 hinj] at h
  linarith

theorem row3083 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L808 + (-1 : ℝ) * HLm Γ 5 L699 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 3, 2, 1, 4] ![0, 3, 2, 1, 4] (by decide) L12047 L12046 (by decide)
  rw [i7457 hinj, i7458 hinj] at h
  linarith

theorem row3084 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L699 + (-1 : ℝ) * HLm Γ 5 L12039 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 4, 2] ![1, 0, 4, 2, 3] (by decide) L12049 L12048 (by decide)
  rw [i7459 hinj, i7460 hinj] at h
  linarith

theorem row3085 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12041 + (-1 : ℝ) * HLm Γ 5 L699 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L12047 L12050 (by decide)
  rw [i7461 hinj, i7458 hinj] at h
  linarith

theorem row3086 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12044 + (-1 : ℝ) * HLm Γ 5 L699 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L12047 L12045 (by decide)
  rw [i7456 hinj, i7458 hinj] at h
  linarith

theorem row3087 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L701 + (-1 : ℝ) * HLm Γ 5 L1488 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L1489 L702 (by decide)
  rw [i307 hinj, i753 hinj] at h
  linarith

theorem row3088 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L1484 + (-1 : ℝ) * HLm Γ 5 L703 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L12052 L12051 (by decide)
  rw [i7462 hinj, i7463 hinj] at h
  linarith

theorem row3089 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L712 + (-1 : ℝ) * HLm Γ 5 L1382 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L1383 L713 (by decide)
  rw [i312 hinj, i690 hinj] at h
  linarith

theorem row3090 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L715 + (-1 : ℝ) * HLm Γ 5 L1392 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L12054 L12053 (by decide)
  rw [i7464 hinj, i7465 hinj] at h
  linarith

theorem row3091 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L1696 + (-1 : ℝ) * HLm Γ 5 L12056 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L12057 L12055 (by decide)
  rw [i7466 hinj, i7467 hinj] at h
  linarith

theorem row3092 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L720 + (-1 : ℝ) * HLm Γ 5 L12056 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L12057 L12058 (by decide)
  rw [i7468 hinj, i7467 hinj] at h
  linarith

theorem row3093 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L733 + (-1 : ℝ) * HLm Γ 5 L1408 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L1409 L12059 (by decide)
  rw [i7469 hinj, i706 hinj] at h
  linarith

theorem row3094 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L1760 + (-1 : ℝ) * HLm Γ 5 L735 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 3, 2, 1, 4] ![0, 3, 2, 1, 4] (by decide) L736 L12060 (by decide)
  rw [i7470 hinj, i323 hinj] at h
  linarith

theorem row3095 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L737 + (-1 : ℝ) * HLm Γ 5 L1404 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L1405 L12061 (by decide)
  rw [i7471 hinj, i704 hinj] at h
  linarith

theorem row3096 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L749 + (-1 : ℝ) * HLm (mirror Γ) 5 L2611 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L2612 L12062 (by decide)
  rw [i1461 hinj', i7472 hinj] at h
  linarith

theorem row3097 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L751 + (-1 : ℝ) * HLm Γ 5 L1534 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L1535 L752 (by decide)
  rw [i331 hinj, i779 hinj] at h
  linarith

theorem row3098 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L1528 + (-1 : ℝ) * HLm Γ 5 L753 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L12064 L12063 (by decide)
  rw [i7473 hinj, i7474 hinj] at h
  linarith

theorem row3099 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L755 + (-1 : ℝ) * HLm (mirror Γ) 5 L705 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 1, 2, 3, 4] ![0, 1, 2, 3, 4] (by decide) L706 L12065 (by decide)
  rw [i309 hinj', i7475 hinj] at h
  linarith

theorem row3100 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L755 + (-1 : ℝ) * HLm (mirror Γ) 5 L159 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L763 L12066 (by decide)
  rw [i337 hinj', i7476 hinj] at h
  linarith

theorem row3101 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L755 + (-1 : ℝ) * HLm (mirror Γ) 5 L7529 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 2, 3, 1, 4] ![0, 3, 1, 2, 4] (by decide) L7530 L12066 (by decide)
  rw [i4457 hinj', i7476 hinj] at h
  linarith

theorem row3102 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L767 + (-1 : ℝ) * HLm (mirror Γ) 5 L767 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L12068 L12067 (by decide)
  rw [i7478 hinj', i7477 hinj] at h
  linarith

theorem row3103 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L767 + (-1 : ℝ) * HLm (mirror Γ) 5 L4206 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 2, 3, 1, 4] ![0, 3, 1, 2, 4] (by decide) L12069 L12067 (by decide)
  rw [i7479 hinj', i7477 hinj] at h
  linarith

theorem row3104 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L767 + (-1 : ℝ) * HLm (mirror Γ) 5 L1363 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![2, 0, 1, 3, 4] ![1, 2, 0, 3, 4] (by decide) L12070 L12067 (by decide)
  rw [i7480 hinj', i7477 hinj] at h
  linarith

theorem row3105 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L767 + (-1 : ℝ) * HLm (mirror Γ) 5 L7263 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![2, 0, 3, 1, 4] ![1, 3, 0, 2, 4] (by decide) L7264 L12067 (by decide)
  rw [i4306 hinj', i7477 hinj] at h
  linarith

theorem row3106 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L767 + (-1 : ℝ) * HLm Γ 5 L11473 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 4, 2] ![1, 0, 4, 2, 3] (by decide) L12071 L12068 (by decide)
  rw [i7478 hinj, i7481 hinj] at h
  linarith

theorem row3107 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L767 + (-1 : ℝ) * HLm Γ 5 L1363 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L12070 L12068 (by decide)
  rw [i7478 hinj, i7480 hinj] at h
  linarith

theorem row3108 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L767 + (-1 : ℝ) * HLm Γ 5 L4214 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 4, 2] ![0, 1, 4, 2, 3] (by decide) L12072 L12068 (by decide)
  rw [i7478 hinj, i7482 hinj] at h
  linarith

theorem row3109 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L4206 + (-1 : ℝ) * HLm Γ 5 L767 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L12068 L12069 (by decide)
  rw [i7479 hinj, i7478 hinj] at h
  linarith

theorem row3110 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L774 + (-1 : ℝ) * HLm (mirror Γ) 5 L1401 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L1402 L12073 (by decide)
  rw [i702 hinj', i7483 hinj] at h
  linarith

theorem row3111 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L4099 + (-1 : ℝ) * HLm Γ 5 L786 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L1621 L12074 (by decide)
  rw [i7484 hinj, i834 hinj] at h
  linarith

theorem row3112 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3891 + (-1 : ℝ) * HLm Γ 5 L790 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L12075 L3892 (by decide)
  rw [i2174 hinj, i7485 hinj] at h
  linarith

theorem row3113 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3585 + (-1 : ℝ) * HLm Γ 5 L790 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 2, 4, 3] ![0, 1, 2, 4, 3] (by decide) L12075 L12076 (by decide)
  rw [i7486 hinj, i7485 hinj] at h
  linarith

theorem row3114 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3719 + (-1 : ℝ) * HLm Γ 5 L1280 = 0 := by
  have h := HLm_permB (Γ := Γ) ![3, 1, 2, 0, 4] ![3, 1, 2, 0, 4] (by decide) L1280 L12077 (by decide)
  rw [i7487 hinj] at h
  linarith

theorem row3115 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L796 + (-1 : ℝ) * HLm Γ 5 L2306 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 3, 2, 1, 4] ![0, 3, 2, 1, 4] (by decide) L12078 L7508 (by decide)
  rw [i4444 hinj, i7488 hinj] at h
  linarith

theorem row3116 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3719 + (-1 : ℝ) * HLm Γ 5 L796 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L796 L3719 (by decide)
  linarith

theorem row3117 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3706 + (-1 : ℝ) * HLm Γ 5 L12079 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 4, 3] ![1, 0, 2, 4, 3] (by decide) L12079 L3707 (by decide)
  rw [i2074 hinj] at h
  linarith

theorem row3118 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3724 + (-1 : ℝ) * HLm Γ 5 L2051 = 0 := by
  have h := HLm_permB (Γ := Γ) ![3, 1, 2, 0, 4] ![3, 1, 2, 0, 4] (by decide) L2052 L3724 (by decide)
  rw [i1125 hinj] at h
  linarith

theorem row3119 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L801 + (-1 : ℝ) * HLm Γ 5 L2305 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 3, 2, 1, 4] ![0, 3, 2, 1, 4] (by decide) L2305 L801 (by decide)
  linarith

theorem row3120 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L801 + (-1 : ℝ) * HLm Γ 5 L12079 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L12079 L801 (by decide)
  linarith

theorem row3121 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3724 + (-1 : ℝ) * HLm Γ 5 L801 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L801 L3724 (by decide)
  linarith

theorem row3122 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11599 + (-1 : ℝ) * HLm Γ 5 L802 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L12081 L12080 (by decide)
  rw [i7489 hinj, i7490 hinj] at h
  linarith

theorem row3123 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11593 + (-1 : ℝ) * HLm Γ 5 L805 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L12083 L12082 (by decide)
  rw [i7491 hinj, i7492 hinj] at h
  linarith

theorem row3124 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L1553 + (-1 : ℝ) * HLm Γ 5 L811 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L12085 L12084 (by decide)
  rw [i7493 hinj, i7494 hinj] at h
  linarith

theorem row3125 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L813 + (-1 : ℝ) * HLm Γ 5 L3226 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L3227 L814 (by decide)
  rw [i365 hinj, i1823 hinj] at h
  linarith

theorem row3126 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12086 + (-1 : ℝ) * HLm Γ 5 L11521 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 4, 2] ![0, 1, 4, 2, 3] (by decide) L11522 L12087 (by decide)
  rw [i7495 hinj, i7044 hinj] at h
  linarith

theorem row3127 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L815 + (-1 : ℝ) * HLm Γ 5 L12086 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 3, 2, 1, 4] ![0, 3, 2, 1, 4] (by decide) L12087 L12088 (by decide)
  rw [i7496 hinj, i7495 hinj] at h
  linarith

theorem row3128 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11517 + (-1 : ℝ) * HLm Γ 5 L12090 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 4, 3, 2] ![0, 1, 4, 3, 2] (by decide) L12091 L12089 (by decide)
  rw [i7497 hinj, i7498 hinj] at h
  linarith

theorem row3129 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12090 + (-1 : ℝ) * HLm Γ 5 L817 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 3, 2, 1, 4] ![0, 3, 2, 1, 4] (by decide) L12093 L12092 (by decide)
  rw [i7499 hinj, i7500 hinj] at h
  linarith

theorem row3130 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L823 + (-1 : ℝ) * HLm Γ 5 L3323 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L3323 L12094 (by decide)
  rw [i7501 hinj] at h
  linarith

theorem row3131 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L825 + (-1 : ℝ) * HLm Γ 5 L2575 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L12095 L844 (by decide)
  rw [i383 hinj, i7502 hinj] at h
  linarith

theorem row3132 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L847 + (-1 : ℝ) * HLm Γ 5 L1719 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L12097 L12096 (by decide)
  rw [i7503 hinj, i7504 hinj] at h
  linarith

theorem row3133 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L851 + (-1 : ℝ) * HLm (mirror Γ) 5 L851 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 1, 2, 3, 4] ![0, 1, 2, 3, 4] (by decide) L12098 L12098 (by decide)
  rw [i7505 hinj', i7505 hinj] at h
  linarith

theorem row3134 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L854 + (-1 : ℝ) * HLm (mirror Γ) 5 L854 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L2501 L12099 (by decide)
  rw [i1385 hinj', i7506 hinj] at h
  linarith

theorem row3135 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3632 + (-1 : ℝ) * HLm Γ 5 L854 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L2501 L12100 (by decide)
  rw [i7507 hinj, i1385 hinj] at h
  linarith

theorem row3136 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L860 + (-1 : ℝ) * HLm (mirror Γ) 5 L860 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L861 L12101 (by decide)
  rw [i392 hinj', i7508 hinj] at h
  linarith

theorem row3137 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L860 + (-1 : ℝ) * HLm (mirror Γ) 5 L3759 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![2, 0, 3, 1, 4] ![1, 3, 0, 2, 4] (by decide) L12103 L12102 (by decide)
  rw [i7510 hinj', i7509 hinj] at h
  linarith

theorem row3138 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3759 + (-1 : ℝ) * HLm Γ 5 L860 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L861 L12104 (by decide)
  rw [i7511 hinj, i392 hinj] at h
  linarith

theorem row3139 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L1187 + (-1 : ℝ) * HLm Γ 5 L863 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L864 L12105 (by decide)
  rw [i7512 hinj, i393 hinj] at h
  linarith

theorem row3140 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L863 + (-1 : ℝ) * HLm Γ 5 L1686 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L12107 L12106 (by decide)
  rw [i7513 hinj, i7514 hinj] at h
  linarith

theorem row3141 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L865 + (-1 : ℝ) * HLm (mirror Γ) 5 L7576 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 2, 3, 4, 1] ![0, 4, 1, 2, 3] (by decide) L7576 L12108 (by decide)
  rw [i7515 hinj] at h
  linarith

theorem row3142 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L865 + (-1 : ℝ) * HLm (mirror Γ) 5 L2124 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![2, 0, 1, 3, 4] ![1, 2, 0, 3, 4] (by decide) L2124 L12108 (by decide)
  rw [i7515 hinj] at h
  linarith

theorem row3143 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L866 + (-1 : ℝ) * HLm (mirror Γ) 5 L1303 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L1304 L12109 (by decide)
  rw [i641 hinj', i7516 hinj] at h
  linarith

theorem row3144 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L866 + (-1 : ℝ) * HLm (mirror Γ) 5 L3230 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 2, 3, 1, 4] ![0, 3, 1, 2, 4] (by decide) L3231 L12109 (by decide)
  rw [i1825 hinj', i7516 hinj] at h
  linarith

theorem row3145 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L866 + (-1 : ℝ) * HLm (mirror Γ) 5 L11304 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![2, 0, 3, 1, 4] ![1, 3, 0, 2, 4] (by decide) L11305 L12110 (by decide)
  rw [i6925 hinj', i7517 hinj] at h
  linarith

theorem row3146 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L866 + (-1 : ℝ) * HLm (mirror Γ) 5 L7957 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![2, 0, 3, 4, 1] ![1, 4, 0, 2, 3] (by decide) L12111 L12110 (by decide)
  rw [i7518 hinj', i7517 hinj] at h
  linarith

theorem row3147 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L1017 + (-1 : ℝ) * HLm Γ 5 L866 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L867 L12112 (by decide)
  rw [i7519 hinj, i394 hinj] at h
  linarith

theorem row3148 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L1668 + (-1 : ℝ) * HLm Γ 5 L870 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L871 L12113 (by decide)
  rw [i7520 hinj, i396 hinj] at h
  linarith

theorem row3149 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L873 + (-1 : ℝ) * HLm Γ 5 L1266 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L1267 L874 (by decide)
  rw [i398 hinj, i618 hinj] at h
  linarith

end EntropyBounds.TwoSet.Certs.R7A5
