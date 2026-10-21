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

theorem row2550 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 11 9 + (-1 : ℝ) * hg Γ 11 8 + (-1 : ℝ) * hg Γ 11 10 := by
  have h := hg_concy hΓ 11 8
  linarith

theorem row2551 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * hg Γ 12 8 + (1 : ℝ) * hg Γ 11 9 + (-1 : ℝ) * hg Γ 11 8 + (-1 : ℝ) * Real.log #Γ := by
  have h := hg_link hΓ hinj 11 8
  linarith

theorem row2552 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 11 10 + (-1 : ℝ) * hg Γ 11 9 + (-1 : ℝ) * hg Γ 11 11 := by
  have h := hg_concy hΓ 11 9
  linarith

theorem row2553 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 11 11 + (-1 : ℝ) * hg Γ 11 10 + (-1 : ℝ) * hg Γ 11 12 := by
  have h := hg_concy hΓ 11 10
  linarith

theorem row2554 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * hg Γ 12 12 + (-1 : ℝ) * hg Γ 11 12 := by
  have h := hg_monox hΓ 11 12
  linarith

theorem row2555 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 12 1 + (-1 : ℝ) * hg Γ 12 0 + (-1 : ℝ) * hg Γ 12 2 := by
  have h := hg_concy hΓ 12 0
  linarith

theorem row2556 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 12 2 + (-1 : ℝ) * hg Γ 12 1 + (-1 : ℝ) * hg Γ 12 3 := by
  have h := hg_concy hΓ 12 1
  linarith

theorem row2557 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 12 3 + (-1 : ℝ) * hg Γ 12 2 + (-1 : ℝ) * hg Γ 12 4 := by
  have h := hg_concy hΓ 12 2
  linarith

theorem row2558 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 12 4 + (-1 : ℝ) * hg Γ 12 3 + (-1 : ℝ) * hg Γ 12 5 := by
  have h := hg_concy hΓ 12 3
  linarith

theorem row2559 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 12 5 + (-1 : ℝ) * hg Γ 12 4 + (-1 : ℝ) * hg Γ 12 6 := by
  have h := hg_concy hΓ 12 4
  linarith

theorem row2560 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 12 6 + (-1 : ℝ) * hg Γ 12 5 + (-1 : ℝ) * hg Γ 12 7 := by
  have h := hg_concy hΓ 12 5
  linarith

theorem row2561 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 12 7 + (-1 : ℝ) * hg Γ 12 6 + (-1 : ℝ) * hg Γ 12 8 := by
  have h := hg_concy hΓ 12 6
  linarith

theorem row2562 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 12 8 + (-1 : ℝ) * hg Γ 12 7 + (-1 : ℝ) * hg Γ 12 9 := by
  have h := hg_concy hΓ 12 7
  linarith

theorem row2563 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 12 9 + (-1 : ℝ) * hg Γ 12 8 + (-1 : ℝ) * hg Γ 12 10 := by
  have h := hg_concy hΓ 12 8
  linarith

theorem row2564 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 12 10 + (-1 : ℝ) * hg Γ 12 9 + (-1 : ℝ) * hg Γ 12 11 := by
  have h := hg_concy hΓ 12 9
  linarith

theorem row2565 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 12 11 + (-1 : ℝ) * hg Γ 12 10 + (-1 : ℝ) * hg Γ 12 12 := by
  have h := hg_concy hΓ 12 10
  linarith

theorem row2566 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * hg Γ 12 12 + (-1 : ℝ) * hg Γ 12 11 := by
  have h := hg_monoy hΓ 12 11
  linarith

theorem row2567 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * hg Γ 3 0 + (-1 : ℝ) * HLm Γ 5 L2836 = 0 := by
  have h := HLm_gridB hΓ F217 3 0 (by decide)
  rw [show [F217] = L2836 from rfl] at h
  unfold hg
  linarith

theorem row2568 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * hg Γ 4 0 + (-1 : ℝ) * HLm Γ 5 L6791 = 0 := by
  have h := HLm_gridB hΓ F219 4 0 (by decide)
  rw [show [F219] = L6791 from rfl] at h
  unfold hg
  linarith

theorem row2569 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * hg Γ 0 1 + (-1 : ℝ) * HLm Γ 5 L3 = 0 := by
  have h := HLm_gridB hΓ F2 0 1 (by decide)
  rw [show [F2] = L3 from rfl] at h
  unfold hg
  linarith

theorem row2570 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * hg Γ 1 1 + (-1 : ℝ) * HLm Γ 5 L11325 = 0 := by
  have h := HLm_gridB hΓ F214 1 1 (by decide)
  rw [show [F214] = L11325 from rfl] at h
  unfold hg
  linarith

theorem row2571 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * hg Γ 2 1 + (-1 : ℝ) * HLm Γ 5 L13 = 0 := by
  have h := HLm_gridB hΓ F6 2 1 (by decide)
  rw [show [F6] = L13 from rfl] at h
  unfold hg
  linarith

theorem row2572 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * hg Γ 3 1 + (-1 : ℝ) * HLm Γ 5 L2838 = 0 := by
  have h := HLm_gridB hΓ F218 3 1 (by decide)
  rw [show [F218] = L2838 from rfl] at h
  unfold hg
  linarith

theorem row2573 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * hg Γ 0 2 + (-1 : ℝ) * HLm Γ 5 L199 = 0 := by
  have h := HLm_gridB hΓ F44 0 2 (by decide)
  rw [show [F44] = L199 from rfl] at h
  unfold hg
  linarith

theorem row2574 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * hg Γ 1 2 + (-1 : ℝ) * HLm Γ 5 L11713 = 0 := by
  have h := HLm_gridB hΓ F66 1 2 (by decide)
  rw [show [F66] = L11713 from rfl] at h
  unfold hg
  linarith

theorem row2575 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * hg Γ 2 2 + (-1 : ℝ) * HLm Γ 5 L503 = 0 := by
  have h := HLm_gridB hΓ F72 2 2 (by decide)
  rw [show [F72] = L503 from rfl] at h
  unfold hg
  linarith

theorem row2576 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L0 + (-1 : ℝ) * HLm (mirror Γ) 5 L15 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 1, 2, 3, 4] ![0, 1, 2, 3, 4] (by decide) L15 L11714 (by decide)
  rw [i7159 hinj] at h
  linarith

theorem row2577 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L0 + (-1 : ℝ) * HLm (mirror Γ) 5 L3 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L3 L11714 (by decide)
  rw [i7159 hinj] at h
  linarith

theorem row2578 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11088 + (-1 : ℝ) * HLm Γ 5 L0 = 0 := by
  have h := HLm_permB (Γ := Γ) ![4, 0, 1, 2, 3] ![1, 2, 3, 4, 0] (by decide) L0 L11088 (by decide)
  linarith

theorem row2579 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2848 + (-1 : ℝ) * HLm Γ 5 L0 = 0 := by
  have h := HLm_permB (Γ := Γ) ![3, 0, 1, 2, 4] ![1, 2, 3, 0, 4] (by decide) L0 L2848 (by decide)
  linarith

theorem row2580 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L38 + (-1 : ℝ) * HLm Γ 5 L0 = 0 := by
  have h := HLm_permB (Γ := Γ) ![2, 0, 1, 3, 4] ![1, 2, 0, 3, 4] (by decide) L0 L38 (by decide)
  linarith

theorem row2581 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L1 + (-1 : ℝ) * HLm Γ 5 L0 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L0 L1 (by decide)
  linarith

theorem row2582 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2980 + (-1 : ℝ) * HLm Γ 5 L7227 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 4, 1, 3, 2] ![0, 2, 4, 3, 1] (by decide) L7227 L2981 (by decide)
  rw [i1699 hinj] at h
  linarith

theorem row2583 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L217 + (-1 : ℝ) * HLm Γ 5 L11715 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 3, 2, 1, 4] ![0, 3, 2, 1, 4] (by decide) L11715 L219 (by decide)
  rw [i77 hinj] at h
  linarith

theorem row2584 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2 + (-1 : ℝ) * HLm (mirror Γ) 5 L16 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 1, 2, 3, 4] ![0, 1, 2, 3, 4] (by decide) L16 L11716 (by decide)
  rw [i7160 hinj] at h
  linarith

theorem row2585 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L103 + (-1 : ℝ) * HLm Γ 5 L2 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L2 L103 (by decide)
  linarith

theorem row2586 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L7227 + (-1 : ℝ) * HLm Γ 5 L2 = 0 := by
  have h := HLm_permB (Γ := Γ) ![3, 1, 0, 2, 4] ![2, 1, 3, 0, 4] (by decide) L2 L11717 (by decide)
  rw [i7161 hinj] at h
  linarith

theorem row2587 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11715 + (-1 : ℝ) * HLm Γ 5 L2 = 0 := by
  have h := HLm_permB (Γ := Γ) ![2, 1, 0, 3, 4] ![2, 1, 0, 3, 4] (by decide) L2 L11718 (by decide)
  rw [i7162 hinj] at h
  linarith

theorem row2588 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3 + (-1 : ℝ) * HLm (mirror Γ) 5 L0 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L0 L11719 (by decide)
  rw [i7163 hinj] at h
  linarith

theorem row2589 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3 + (-1 : ℝ) * HLm (mirror Γ) 5 L1 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 1, 2, 3, 4] ![0, 1, 2, 3, 4] (by decide) L1 L11719 (by decide)
  rw [i7163 hinj] at h
  linarith

theorem row2590 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3 + (-1 : ℝ) * HLm (mirror Γ) 5 L38 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L38 L11719 (by decide)
  rw [i7163 hinj] at h
  linarith

theorem row2591 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3 + (-1 : ℝ) * HLm (mirror Γ) 5 L2848 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 2, 3, 1, 4] ![0, 3, 1, 2, 4] (by decide) L2848 L11719 (by decide)
  rw [i7163 hinj] at h
  linarith

theorem row2592 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3 + (-1 : ℝ) * HLm (mirror Γ) 5 L11088 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 2, 3, 4, 1] ![0, 4, 1, 2, 3] (by decide) L11088 L11719 (by decide)
  rw [i7163 hinj] at h
  linarith

theorem row2593 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3 + (-1 : ℝ) * HLm Γ 5 L15 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L15 L3 (by decide)
  linarith

theorem row2594 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2860 + (-1 : ℝ) * HLm Γ 5 L108 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 3, 1, 2, 4] ![0, 2, 3, 1, 4] (by decide) L109 L2861 (by decide)
  rw [i1636 hinj, i30 hinj] at h
  linarith

theorem row2595 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L110 + (-1 : ℝ) * HLm Γ 5 L108 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L109 L116 (by decide)
  rw [i32 hinj, i30 hinj] at h
  linarith

theorem row2596 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L4 + (-1 : ℝ) * HLm (mirror Γ) 5 L108 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 1, 2, 3, 4] ![0, 1, 2, 3, 4] (by decide) L109 L11720 (by decide)
  rw [i30 hinj', i7164 hinj] at h
  linarith

theorem row2597 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L4 + (-1 : ℝ) * HLm (mirror Γ) 5 L110 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L110 L11721 (by decide)
  rw [i7165 hinj] at h
  linarith

theorem row2598 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L4 + (-1 : ℝ) * HLm (mirror Γ) 5 L4 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L4 L11720 (by decide)
  rw [i7164 hinj] at h
  linarith

theorem row2599 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L4 + (-1 : ℝ) * HLm (mirror Γ) 5 L7351 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![2, 0, 3, 1, 4] ![1, 3, 0, 2, 4] (by decide) L7351 L11721 (by decide)
  rw [i7165 hinj] at h
  linarith

theorem row2600 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L108 + (-1 : ℝ) * HLm Γ 5 L4 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L4 L109 (by decide)
  rw [i30 hinj] at h
  linarith

theorem row2601 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L5 + (-1 : ℝ) * HLm (mirror Γ) 5 L22 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L22 L11722 (by decide)
  rw [i7166 hinj] at h
  linarith

theorem row2602 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L5 + (-1 : ℝ) * HLm (mirror Γ) 5 L5 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 1, 2, 3, 4] ![0, 1, 2, 3, 4] (by decide) L5 L11722 (by decide)
  rw [i7166 hinj] at h
  linarith

theorem row2603 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L5 + (-1 : ℝ) * HLm Γ 5 L22 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L22 L5 (by decide)
  linarith

theorem row2604 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2906 + (-1 : ℝ) * HLm Γ 5 L2010 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 3, 1, 2, 4] ![0, 2, 3, 1, 4] (by decide) L2011 L2907 (by decide)
  rw [i1659 hinj, i1101 hinj] at h
  linarith

theorem row2605 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L307 + (-1 : ℝ) * HLm Γ 5 L2010 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L2011 L2903 (by decide)
  rw [i1657 hinj, i1101 hinj] at h
  linarith

theorem row2606 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L6 + (-1 : ℝ) * HLm (mirror Γ) 5 L623 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 1, 2, 3, 4] ![0, 1, 2, 3, 4] (by decide) L623 L11723 (by decide)
  rw [i7167 hinj] at h
  linarith

theorem row2607 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3691 + (-1 : ℝ) * HLm Γ 5 L6 = 0 := by
  have h := HLm_permB (Γ := Γ) ![2, 1, 0, 3, 4] ![2, 1, 0, 3, 4] (by decide) L6 L11724 (by decide)
  rw [i7168 hinj] at h
  linarith

theorem row2608 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2010 + (-1 : ℝ) * HLm Γ 5 L6 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L6 L2011 (by decide)
  rw [i1101 hinj] at h
  linarith

theorem row2609 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L7 + (-1 : ℝ) * HLm (mirror Γ) 5 L26 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L27 L8 (by decide)
  rw [i5 hinj', i0 hinj] at h
  linarith

theorem row2610 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L7 + (-1 : ℝ) * HLm (mirror Γ) 5 L7 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 1, 2, 3, 4] ![0, 1, 2, 3, 4] (by decide) L8 L8 (by decide)
  rw [i0 hinj', i0 hinj] at h
  linarith

theorem row2611 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L7 + (-1 : ℝ) * HLm Γ 5 L26 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L27 L8 (by decide)
  rw [i0 hinj, i5 hinj] at h
  linarith

theorem row2612 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3009 + (-1 : ℝ) * HLm Γ 5 L258 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 4, 1, 2, 3] ![0, 2, 3, 4, 1] (by decide) L11726 L11725 (by decide)
  rw [i7169 hinj, i7170 hinj] at h
  linarith

theorem row2613 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3563 + (-1 : ℝ) * HLm Γ 5 L258 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 3, 1, 2, 4] ![0, 2, 3, 1, 4] (by decide) L11726 L11727 (by decide)
  rw [i7171 hinj, i7170 hinj] at h
  linarith

theorem row2614 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L576 + (-1 : ℝ) * HLm Γ 5 L258 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L11726 L11728 (by decide)
  rw [i7172 hinj, i7170 hinj] at h
  linarith

theorem row2615 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L9 + (-1 : ℝ) * HLm (mirror Γ) 5 L6813 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L11730 L11729 (by decide)
  rw [i7174 hinj', i7173 hinj] at h
  linarith

theorem row2616 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L9 + (-1 : ℝ) * HLm (mirror Γ) 5 L17 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 1, 2, 3, 4] ![0, 1, 2, 3, 4] (by decide) L18 L11729 (by decide)
  rw [i2 hinj', i7173 hinj] at h
  linarith

theorem row2617 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L691 + (-1 : ℝ) * HLm Γ 5 L9 = 0 := by
  have h := HLm_permB (Γ := Γ) ![2, 1, 0, 3, 4] ![2, 1, 0, 3, 4] (by decide) L10 L11731 (by decide)
  rw [i7175 hinj, i1 hinj] at h
  linarith

theorem row2618 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L258 + (-1 : ℝ) * HLm Γ 5 L9 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L10 L11726 (by decide)
  rw [i7170 hinj, i1 hinj] at h
  linarith

theorem row2619 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11 + (-1 : ℝ) * HLm (mirror Γ) 5 L53 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![2, 0, 1, 3, 4] ![1, 2, 0, 3, 4] (by decide) L53 L11732 (by decide)
  rw [i7176 hinj] at h
  linarith

theorem row2620 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11 + (-1 : ℝ) * HLm (mirror Γ) 5 L2850 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![2, 0, 3, 1, 4] ![1, 3, 0, 2, 4] (by decide) L2850 L11732 (by decide)
  rw [i7176 hinj] at h
  linarith

theorem row2621 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11 + (-1 : ℝ) * HLm (mirror Γ) 5 L31 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![1, 2, 0, 3, 4] ![2, 0, 1, 3, 4] (by decide) L31 L11732 (by decide)
  rw [i7176 hinj] at h
  linarith

theorem row2622 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11 + (-1 : ℝ) * HLm (mirror Γ) 5 L11 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L11 L11732 (by decide)
  rw [i7176 hinj] at h
  linarith

theorem row2623 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11 + (-1 : ℝ) * HLm (mirror Γ) 5 L11325 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 2, 3, 4, 1] ![0, 4, 1, 2, 3] (by decide) L11325 L11732 (by decide)
  rw [i7176 hinj] at h
  linarith

theorem row2624 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11 + (-1 : ℝ) * HLm Γ 5 L31 = 0 := by
  have h := HLm_permB (Γ := Γ) ![2, 1, 0, 3, 4] ![2, 1, 0, 3, 4] (by decide) L31 L11 (by decide)
  linarith

theorem row2625 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2850 + (-1 : ℝ) * HLm Γ 5 L11 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L11 L2850 (by decide)
  linarith

theorem row2626 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11 + (-1 : ℝ) * HLm Γ 5 L53 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L53 L11 (by decide)
  linarith

theorem row2627 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11 + (-1 : ℝ) * HLm Γ 5 L11325 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 4, 2] ![0, 1, 4, 2, 3] (by decide) L11325 L11 (by decide)
  linarith

theorem row2628 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L54 + (-1 : ℝ) * HLm Γ 5 L11 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L11 L54 (by decide)
  linarith

theorem row2629 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L485 + (-1 : ℝ) * HLm Γ 5 L7234 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L7235 L11733 (by decide)
  rw [i7177 hinj, i4289 hinj] at h
  linarith

theorem row2630 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L241 + (-1 : ℝ) * HLm Γ 5 L11734 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 3, 2, 1, 4] ![0, 3, 2, 1, 4] (by decide) L11735 L242 (by decide)
  rw [i87 hinj, i7178 hinj] at h
  linarith

theorem row2631 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2913 + (-1 : ℝ) * HLm Γ 5 L11736 = 0 := by
  have h := HLm_permB (Γ := Γ) ![4, 1, 2, 3, 0] ![4, 1, 2, 3, 0] (by decide) L11736 L2914 (by decide)
  rw [i1662 hinj] at h
  linarith

theorem row2632 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2985 + (-1 : ℝ) * HLm Γ 5 L11736 = 0 := by
  have h := HLm_permB (Γ := Γ) ![3, 1, 0, 2, 4] ![2, 1, 3, 0, 4] (by decide) L11736 L11737 (by decide)
  rw [i7179 hinj] at h
  linarith

theorem row2633 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3186 + (-1 : ℝ) * HLm Γ 5 L105 = 0 := by
  have h := HLm_permB (Γ := Γ) ![2, 1, 0, 3, 4] ![2, 1, 0, 3, 4] (by decide) L105 L11738 (by decide)
  rw [i7180 hinj] at h
  linarith

theorem row2634 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12 + (-1 : ℝ) * HLm (mirror Γ) 5 L3088 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![2, 0, 1, 3, 4] ![1, 2, 0, 3, 4] (by decide) L6913 L11739 (by decide)
  rw [i4111 hinj', i7181 hinj] at h
  linarith

theorem row2635 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12 + (-1 : ℝ) * HLm (mirror Γ) 5 L7358 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![2, 0, 3, 1, 4] ![1, 3, 0, 2, 4] (by decide) L7359 L11739 (by decide)
  rw [i4360 hinj', i7181 hinj] at h
  linarith

theorem row2636 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12 + (-1 : ℝ) * HLm (mirror Γ) 5 L117 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 2, 3, 1, 4] ![0, 3, 1, 2, 4] (by decide) L117 L11739 (by decide)
  rw [i7181 hinj] at h
  linarith

theorem row2637 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12 + (-1 : ℝ) * HLm (mirror Γ) 5 L11230 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![2, 0, 3, 4, 1] ![1, 4, 0, 2, 3] (by decide) L11231 L11739 (by decide)
  rw [i6883 hinj', i7181 hinj] at h
  linarith

theorem row2638 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L180 + (-1 : ℝ) * HLm Γ 5 L12 = 0 := by
  have h := HLm_permB (Γ := Γ) ![2, 1, 0, 3, 4] ![2, 1, 0, 3, 4] (by decide) L12 L2026 (by decide)
  rw [i1109 hinj] at h
  linarith

theorem row2639 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L7234 + (-1 : ℝ) * HLm Γ 5 L12 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) L12 L7235 (by decide)
  rw [i4289 hinj] at h
  linarith

theorem row2640 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L11734 + (-1 : ℝ) * HLm Γ 5 L12 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L12 L11735 (by decide)
  rw [i7178 hinj] at h
  linarith

theorem row2641 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L12 + (-1 : ℝ) * HLm Γ 5 L11736 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 4, 2] ![0, 1, 4, 2, 3] (by decide) L11736 L12 (by decide)
  linarith

theorem row2642 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L105 + (-1 : ℝ) * HLm Γ 5 L12 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L12 L105 (by decide)
  linarith

theorem row2643 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L549 + (-1 : ℝ) * HLm Γ 5 L32 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L32 L549 (by decide)
  linarith

theorem row2644 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L13 + (-1 : ℝ) * HLm (mirror Γ) 5 L387 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![2, 3, 1, 0, 4] ![3, 2, 0, 1, 4] (by decide) L387 L11740 (by decide)
  rw [i7182 hinj] at h
  linarith

theorem row2645 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L13 + (-1 : ℝ) * HLm Γ 5 L68 = 0 := by
  have h := HLm_permB (Γ := Γ) ![3, 1, 2, 0, 4] ![3, 1, 2, 0, 4] (by decide) L68 L13 (by decide)
  linarith

theorem row2646 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L13 + (-1 : ℝ) * HLm Γ 5 L32 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L32 L13 (by decide)
  linarith

theorem row2647 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L491 + (-1 : ℝ) * HLm Γ 5 L3080 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 4, 2] ![0, 1, 4, 2, 3] (by decide) L11742 L11741 (by decide)
  rw [i7183 hinj, i7184 hinj] at h
  linarith

theorem row2648 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3191 + (-1 : ℝ) * HLm Γ 5 L14 = 0 := by
  have h := HLm_permB (Γ := Γ) ![4, 1, 2, 3, 0] ![4, 1, 2, 3, 0] (by decide) L14 L3192 (by decide)
  rw [i1805 hinj] at h
  linarith

theorem row2649 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L368 + (-1 : ℝ) * HLm Γ 5 L14 = 0 := by
  have h := HLm_permB (Γ := Γ) ![3, 1, 2, 0, 4] ![3, 1, 2, 0, 4] (by decide) L14 L378 (by decide)
  rw [i152 hinj] at h
  linarith

theorem row2650 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L491 + (-1 : ℝ) * HLm Γ 5 L14 = 0 := by
  have h := HLm_permB (Γ := Γ) ![2, 1, 0, 3, 4] ![2, 1, 0, 3, 4] (by decide) L14 L11741 (by decide)
  rw [i7183 hinj] at h
  linarith

theorem row2651 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L16 + (-1 : ℝ) * HLm (mirror Γ) 5 L2 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 1, 2, 3, 4] ![0, 1, 2, 3, 4] (by decide) L2 L11743 (by decide)
  rw [i7185 hinj] at h
  linarith

theorem row2652 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L16 + (-1 : ℝ) * HLm (mirror Γ) 5 L103 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L103 L11743 (by decide)
  rw [i7185 hinj] at h
  linarith

theorem row2653 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L16 + (-1 : ℝ) * HLm (mirror Γ) 5 L6931 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 2, 3, 1, 4] ![0, 3, 1, 2, 4] (by decide) L6931 L11743 (by decide)
  rw [i7185 hinj] at h
  linarith

theorem row2654 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L16 + (-1 : ℝ) * HLm (mirror Γ) 5 L6804 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 2, 3, 4, 1] ![0, 4, 1, 2, 3] (by decide) L6804 L11743 (by decide)
  rw [i7185 hinj] at h
  linarith

theorem row2655 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L16 + (-1 : ℝ) * HLm (mirror Γ) 5 L7227 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![2, 0, 3, 1, 4] ![1, 3, 0, 2, 4] (by decide) L7227 L11743 (by decide)
  rw [i7185 hinj] at h
  linarith

theorem row2656 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L16 + (-1 : ℝ) * HLm (mirror Γ) 5 L217 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![2, 3, 0, 1, 4] ![2, 3, 0, 1, 4] (by decide) L217 L11743 (by decide)
  rw [i7185 hinj] at h
  linarith

theorem row2657 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L16 + (-1 : ℝ) * HLm (mirror Γ) 5 L2980 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![2, 3, 4, 0, 1] ![3, 4, 0, 1, 2] (by decide) L2980 L11743 (by decide)
  rw [i7185 hinj] at h
  linarith

theorem row2658 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L17 + (-1 : ℝ) * HLm (mirror Γ) 5 L258 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L11726 L11744 (by decide)
  rw [i7170 hinj', i7186 hinj] at h
  linarith

theorem row2659 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L17 + (-1 : ℝ) * HLm (mirror Γ) 5 L576 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![1, 2, 0, 3, 4] ![2, 0, 1, 3, 4] (by decide) L6881 L11745 (by decide)
  rw [i4093 hinj', i7187 hinj] at h
  linarith

theorem row2660 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L17 + (-1 : ℝ) * HLm (mirror Γ) 5 L3563 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![1, 2, 3, 0, 4] ![3, 0, 1, 2, 4] (by decide) L11746 L11745 (by decide)
  rw [i7188 hinj', i7187 hinj] at h
  linarith

theorem row2661 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L17 + (-1 : ℝ) * HLm (mirror Γ) 5 L3009 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![1, 2, 3, 4, 0] ![4, 0, 1, 2, 3] (by decide) L11747 L11745 (by decide)
  rw [i7189 hinj', i7187 hinj] at h
  linarith

theorem row2662 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L17 + (-1 : ℝ) * HLm (mirror Γ) 5 L9 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 1, 2, 3, 4] ![0, 1, 2, 3, 4] (by decide) L10 L11744 (by decide)
  rw [i1 hinj', i7186 hinj] at h
  linarith

theorem row2663 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L19 + (-1 : ℝ) * HLm Γ 5 L84 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L84 L19 (by decide)
  linarith

theorem row2664 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L523 + (-1 : ℝ) * HLm Γ 5 L20 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L21 L11748 (by decide)
  rw [i7190 hinj, i3 hinj] at h
  linarith

theorem row2665 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L23 + (-1 : ℝ) * HLm (mirror Γ) 5 L686 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L6888 L11749 (by decide)
  rw [i4098 hinj', i7191 hinj] at h
  linarith

theorem row2666 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L686 + (-1 : ℝ) * HLm Γ 5 L23 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L24 L6880 (by decide)
  rw [i4092 hinj, i4 hinj] at h
  linarith

theorem row2667 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L25 + (-1 : ℝ) * HLm (mirror Γ) 5 L25 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L25 L11750 (by decide)
  rw [i7192 hinj] at h
  linarith

theorem row2668 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L25 + (-1 : ℝ) * HLm (mirror Γ) 5 L234 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![2, 0, 1, 3, 4] ![1, 2, 0, 3, 4] (by decide) L2063 L11750 (by decide)
  rw [i1131 hinj', i7192 hinj] at h
  linarith

theorem row2669 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L234 + (-1 : ℝ) * HLm Γ 5 L25 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L25 L2063 (by decide)
  rw [i1131 hinj] at h
  linarith

theorem row2670 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L161 + (-1 : ℝ) * HLm Γ 5 L25 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L25 L161 (by decide)
  linarith

theorem row2671 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L28 + (-1 : ℝ) * HLm Γ 5 L72 = 0 := by
  have h := HLm_permB (Γ := Γ) ![3, 1, 2, 0, 4] ![3, 1, 2, 0, 4] (by decide) L72 L28 (by decide)
  linarith

theorem row2672 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L86 + (-1 : ℝ) * HLm Γ 5 L29 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L30 L11751 (by decide)
  rw [i7193 hinj, i6 hinj] at h
  linarith

theorem row2673 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2838 + (-1 : ℝ) * HLm Γ 5 L81 = 0 := by
  have h := HLm_permB (Γ := Γ) ![4, 1, 2, 3, 0] ![4, 1, 2, 3, 0] (by decide) L81 L2838 (by decide)
  linarith

theorem row2674 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L34 + (-1 : ℝ) * HLm Γ 5 L81 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L81 L34 (by decide)
  linarith

theorem row2675 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L489 + (-1 : ℝ) * HLm Γ 5 L35 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L35 L490 (by decide)
  rw [i204 hinj] at h
  linarith

theorem row2676 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L36 + (-1 : ℝ) * HLm Γ 5 L85 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L85 L36 (by decide)
  linarith

theorem row2677 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L538 + (-1 : ℝ) * HLm Γ 5 L37 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L37 L539 (by decide)
  rw [i226 hinj] at h
  linarith

theorem row2678 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L39 + (-1 : ℝ) * HLm (mirror Γ) 5 L59 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L59 L39 (by decide)
  linarith

theorem row2679 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L3015 + (-1 : ℝ) * HLm Γ 5 L40 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L41 L3016 (by decide)
  rw [i1716 hinj, i7 hinj] at h
  linarith

theorem row2680 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L42 + (-1 : ℝ) * HLm Γ 5 L332 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L332 L42 (by decide)
  linarith

theorem row2681 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L43 + (-1 : ℝ) * HLm Γ 5 L3065 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 4, 2] ![0, 1, 4, 2, 3] (by decide) L3066 L44 (by decide)
  rw [i8 hinj, i1744 hinj] at h
  linarith

theorem row2682 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L329 + (-1 : ℝ) * HLm Γ 5 L43 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L44 L2982 (by decide)
  rw [i1700 hinj, i8 hinj] at h
  linarith

theorem row2683 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L45 + (-1 : ℝ) * HLm (mirror Γ) 5 L73 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![3, 1, 0, 2, 4] ![2, 1, 3, 0, 4] (by decide) L73 L11752 (by decide)
  rw [i7194 hinj] at h
  linarith

theorem row2684 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L45 + (-1 : ℝ) * HLm (mirror Γ) 5 L45 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![3, 1, 2, 0, 4] ![3, 1, 2, 0, 4] (by decide) L45 L11752 (by decide)
  rw [i7194 hinj] at h
  linarith

theorem row2685 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L45 + (-1 : ℝ) * HLm Γ 5 L73 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L73 L45 (by decide)
  linarith

theorem row2686 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L540 + (-1 : ℝ) * HLm Γ 5 L46 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L47 L11753 (by decide)
  rw [i7195 hinj, i9 hinj] at h
  linarith

theorem row2687 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2126 + (-1 : ℝ) * HLm Γ 5 L46 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L47 L2986 (by decide)
  rw [i1702 hinj, i9 hinj] at h
  linarith

theorem row2688 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L48 + (-1 : ℝ) * HLm Γ 5 L420 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L420 L48 (by decide)
  linarith

theorem row2689 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L49 + (-1 : ℝ) * HLm Γ 5 L3133 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 4, 2] ![0, 1, 4, 2, 3] (by decide) L11754 L50 (by decide)
  rw [i10 hinj, i7196 hinj] at h
  linarith

theorem row2690 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L417 + (-1 : ℝ) * HLm Γ 5 L49 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L50 L3132 (by decide)
  rw [i1776 hinj, i10 hinj] at h
  linarith

theorem row2691 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L51 + (-1 : ℝ) * HLm (mirror Γ) 5 L199 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L199 L11755 (by decide)
  rw [i7197 hinj] at h
  linarith

theorem row2692 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L51 + (-1 : ℝ) * HLm Γ 5 L136 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) L136 L51 (by decide)
  linarith

theorem row2693 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L456 + (-1 : ℝ) * HLm Γ 5 L51 = 0 := by
  have h := HLm_permB (Γ := Γ) ![3, 0, 2, 1, 4] ![1, 3, 2, 0, 4] (by decide) L51 L456 (by decide)
  linarith

theorem row2694 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L1959 + (-1 : ℝ) * HLm Γ 5 L51 = 0 := by
  have h := HLm_permB (Γ := Γ) ![1, 0, 2, 3, 4] ![1, 0, 2, 3, 4] (by decide) L51 L1959 (by decide)
  linarith

theorem row2695 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L51 + (-1 : ℝ) * HLm Γ 5 L3014 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 4, 2] ![0, 1, 4, 2, 3] (by decide) L3014 L51 (by decide)
  linarith

theorem row2696 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2998 + (-1 : ℝ) * HLm Γ 5 L51 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L51 L2998 (by decide)
  linarith

theorem row2697 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L400 + (-1 : ℝ) * HLm Γ 5 L52 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 2, 4] ![0, 1, 3, 2, 4] (by decide) L52 L400 (by decide)
  linarith

theorem row2698 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L55 + (-1 : ℝ) * HLm (mirror Γ) 5 L55 = 0 := by
  have hΓ' := mirror_nonempty hΓ
  have hinj' := mirror_inj hinj
  have h := HLm_mirror_permB Γ ![2, 3, 0, 1, 4] ![2, 3, 0, 1, 4] (by decide) L55 L11756 (by decide)
  rw [i7198 hinj] at h
  linarith

theorem row2699 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L55 + (-1 : ℝ) * HLm Γ 5 L3857 = 0 := by
  have h := HLm_permB (Γ := Γ) ![0, 1, 3, 4, 2] ![0, 1, 4, 2, 3] (by decide) L3858 L11757 (by decide)
  rw [i7199 hinj, i2155 hinj] at h
  linarith

end EntropyBounds.TwoSet.Certs.R7A5
