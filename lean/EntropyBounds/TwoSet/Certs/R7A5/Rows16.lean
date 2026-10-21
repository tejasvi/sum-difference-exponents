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

theorem row2400 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L851 + (-1 : ℝ) * HLm Γ 5 L26 + (-1 : ℝ) * HLm Γ 5 L7 = 0 := by
  have h := HLm_indepB hΓ (l₁ := L26) (l₂ := L7) [0] (by decide) (by decide)
  rw [show L26 ++ L7 = L851 from rfl] at h
  linarith

theorem row2401 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L1451 + (-1 : ℝ) * HLm Γ 5 L851 + (-1 : ℝ) * HLm Γ 5 L38 = 0 := by
  have h := HLm_indepB hΓ (l₁ := L851) (l₂ := L38) [0, 1] (by decide) (by decide)
  rw [show L851 ++ L38 = L1451 from rfl] at h
  linarith

theorem row2402 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L1451 + (-1 : ℝ) * HLm Γ 5 L2848 = 0 := by
  have h := HLm_indepB hΓ (l₁ := L1451) (l₂ := L2848) [0, 1, 2] (by decide) (by decide)
  rw [show L1451 ++ L2848 = L1044 from rfl] at h
  linarith

theorem row2403 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L11088 = 0 := by
  have h := HLm_indepB hΓ (l₁ := L1044) (l₂ := L11088) [0, 1, 2, 3] (by decide) (by decide)
  rw [show L1044 ++ L11088 = L2831 from rfl] at h
  linarith

theorem row2404 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * Real.log #(X + Y) + (-1 : ℝ) * HLm Γ 5 L22 := by
  have h := HLm_bsumB hΓ hXY F9 0 0 (by decide)
  rw [show [F9] = L22 from rfl] at h
  linarith

theorem row2405 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * Real.log #(X + Y) + (-1 : ℝ) * HLm Γ 5 L31 := by
  have h := HLm_bsumB hΓ hXY F12 0 1 (by decide)
  rw [show [F12] = L31 from rfl] at h
  linarith

theorem row2406 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    (1 : ℝ) * Real.log #Γ + (-1 : ℝ) * HLm Γ 5 L26 = 0 := by
  have h := HLm_pairKB hΓ 0 L26 (by decide)
  linarith

theorem row2407 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * hg Γ 1 1 + (1 : ℝ) * hg Γ 0 2 + (-1 : ℝ) * hg Γ 0 1 + (-1 : ℝ) * Real.log #Γ := by
  have h := hg_link hΓ hinj 0 1
  linarith

theorem row2408 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 1 3 + (-1 : ℝ) * hg Γ 0 3 + (-1 : ℝ) * hg Γ 2 3 := by
  have h := hg_concx hΓ 0 3
  linarith

theorem row2409 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 1 4 + (-1 : ℝ) * hg Γ 0 4 + (-1 : ℝ) * hg Γ 2 4 := by
  have h := hg_concx hΓ 0 4
  linarith

theorem row2410 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * hg Γ 1 4 + (1 : ℝ) * hg Γ 0 5 + (-1 : ℝ) * hg Γ 0 4 + (-1 : ℝ) * Real.log #Γ := by
  have h := hg_link hΓ hinj 0 4
  linarith

theorem row2411 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 1 5 + (-1 : ℝ) * hg Γ 0 5 + (-1 : ℝ) * hg Γ 2 5 := by
  have h := hg_concx hΓ 0 5
  linarith

theorem row2412 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * hg Γ 1 5 + (1 : ℝ) * hg Γ 0 6 + (-1 : ℝ) * hg Γ 0 5 + (-1 : ℝ) * Real.log #Γ := by
  have h := hg_link hΓ hinj 0 5
  linarith

theorem row2413 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 1 6 + (-1 : ℝ) * hg Γ 0 6 + (-1 : ℝ) * hg Γ 2 6 := by
  have h := hg_concx hΓ 0 6
  linarith

theorem row2414 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * hg Γ 1 6 + (1 : ℝ) * hg Γ 0 7 + (-1 : ℝ) * hg Γ 0 6 + (-1 : ℝ) * Real.log #Γ := by
  have h := hg_link hΓ hinj 0 6
  linarith

theorem row2415 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 1 7 + (-1 : ℝ) * hg Γ 0 7 + (-1 : ℝ) * hg Γ 2 7 := by
  have h := hg_concx hΓ 0 7
  linarith

theorem row2416 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * hg Γ 1 7 + (1 : ℝ) * hg Γ 0 8 + (-1 : ℝ) * hg Γ 0 7 + (-1 : ℝ) * Real.log #Γ := by
  have h := hg_link hΓ hinj 0 7
  linarith

theorem row2417 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 1 8 + (-1 : ℝ) * hg Γ 0 8 + (-1 : ℝ) * hg Γ 2 8 := by
  have h := hg_concx hΓ 0 8
  linarith

theorem row2418 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * hg Γ 1 8 + (1 : ℝ) * hg Γ 0 9 + (-1 : ℝ) * hg Γ 0 8 + (-1 : ℝ) * Real.log #Γ := by
  have h := hg_link hΓ hinj 0 8
  linarith

theorem row2419 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 1 9 + (-1 : ℝ) * hg Γ 0 9 + (-1 : ℝ) * hg Γ 2 9 := by
  have h := hg_concx hΓ 0 9
  linarith

theorem row2420 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * hg Γ 1 9 + (1 : ℝ) * hg Γ 0 10 + (-1 : ℝ) * hg Γ 0 9 + (-1 : ℝ) * Real.log #Γ := by
  have h := hg_link hΓ hinj 0 9
  linarith

theorem row2421 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * hg Γ 1 10 + (1 : ℝ) * hg Γ 0 11 + (-1 : ℝ) * hg Γ 0 10 + (-1 : ℝ) * Real.log #Γ := by
  have h := hg_link hΓ hinj 0 10
  linarith

theorem row2422 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * hg Γ 1 11 + (1 : ℝ) * hg Γ 0 12 + (-1 : ℝ) * hg Γ 0 11 + (-1 : ℝ) * Real.log #Γ := by
  have h := hg_link hΓ hinj 0 11
  linarith

theorem row2423 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 1 12 + (-1 : ℝ) * hg Γ 0 12 + (-1 : ℝ) * hg Γ 2 12 := by
  have h := hg_concx hΓ 0 12
  linarith

theorem row2424 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 2 2 + (-1 : ℝ) * hg Γ 1 2 + (-1 : ℝ) * hg Γ 3 2 := by
  have h := hg_concx hΓ 1 2
  linarith

theorem row2425 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 2 3 + (-1 : ℝ) * hg Γ 1 3 + (-1 : ℝ) * hg Γ 3 3 := by
  have h := hg_concx hΓ 1 3
  linarith

theorem row2426 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 2 4 + (-1 : ℝ) * hg Γ 1 4 + (-1 : ℝ) * hg Γ 3 4 := by
  have h := hg_concx hΓ 1 4
  linarith

theorem row2427 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 2 5 + (-1 : ℝ) * hg Γ 1 5 + (-1 : ℝ) * hg Γ 3 5 := by
  have h := hg_concx hΓ 1 5
  linarith

theorem row2428 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 2 6 + (-1 : ℝ) * hg Γ 1 6 + (-1 : ℝ) * hg Γ 3 6 := by
  have h := hg_concx hΓ 1 6
  linarith

theorem row2429 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 2 7 + (-1 : ℝ) * hg Γ 1 7 + (-1 : ℝ) * hg Γ 3 7 := by
  have h := hg_concx hΓ 1 7
  linarith

theorem row2430 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 2 8 + (-1 : ℝ) * hg Γ 1 8 + (-1 : ℝ) * hg Γ 3 8 := by
  have h := hg_concx hΓ 1 8
  linarith

theorem row2431 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 2 9 + (-1 : ℝ) * hg Γ 1 9 + (-1 : ℝ) * hg Γ 3 9 := by
  have h := hg_concx hΓ 1 9
  linarith

theorem row2432 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 2 10 + (-1 : ℝ) * hg Γ 1 10 + (-1 : ℝ) * hg Γ 3 10 := by
  have h := hg_concx hΓ 1 10
  linarith

theorem row2433 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 2 11 + (-1 : ℝ) * hg Γ 1 11 + (-1 : ℝ) * hg Γ 3 11 := by
  have h := hg_concx hΓ 1 11
  linarith

theorem row2434 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 2 12 + (-1 : ℝ) * hg Γ 1 12 + (-1 : ℝ) * hg Γ 3 12 := by
  have h := hg_concx hΓ 1 12
  linarith

theorem row2435 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 2 2 + (-1 : ℝ) * hg Γ 2 1 + (-1 : ℝ) * hg Γ 2 3 := by
  have h := hg_concy hΓ 2 1
  linarith

theorem row2436 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 3 3 + (-1 : ℝ) * hg Γ 2 3 + (-1 : ℝ) * hg Γ 4 3 := by
  have h := hg_concx hΓ 2 3
  linarith

theorem row2437 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 3 4 + (-1 : ℝ) * hg Γ 2 4 + (-1 : ℝ) * hg Γ 4 4 := by
  have h := hg_concx hΓ 2 4
  linarith

theorem row2438 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 3 5 + (-1 : ℝ) * hg Γ 2 5 + (-1 : ℝ) * hg Γ 4 5 := by
  have h := hg_concx hΓ 2 5
  linarith

theorem row2439 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 3 6 + (-1 : ℝ) * hg Γ 2 6 + (-1 : ℝ) * hg Γ 4 6 := by
  have h := hg_concx hΓ 2 6
  linarith

theorem row2440 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 3 7 + (-1 : ℝ) * hg Γ 2 7 + (-1 : ℝ) * hg Γ 4 7 := by
  have h := hg_concx hΓ 2 7
  linarith

theorem row2441 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 3 8 + (-1 : ℝ) * hg Γ 2 8 + (-1 : ℝ) * hg Γ 4 8 := by
  have h := hg_concx hΓ 2 8
  linarith

theorem row2442 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 3 9 + (-1 : ℝ) * hg Γ 2 9 + (-1 : ℝ) * hg Γ 4 9 := by
  have h := hg_concx hΓ 2 9
  linarith

theorem row2443 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 3 10 + (-1 : ℝ) * hg Γ 2 10 + (-1 : ℝ) * hg Γ 4 10 := by
  have h := hg_concx hΓ 2 10
  linarith

theorem row2444 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 3 11 + (-1 : ℝ) * hg Γ 2 11 + (-1 : ℝ) * hg Γ 4 11 := by
  have h := hg_concx hΓ 2 11
  linarith

theorem row2445 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 3 12 + (-1 : ℝ) * hg Γ 2 12 + (-1 : ℝ) * hg Γ 4 12 := by
  have h := hg_concx hΓ 2 12
  linarith

theorem row2446 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 3 1 + (-1 : ℝ) * hg Γ 3 0 + (-1 : ℝ) * hg Γ 3 2 := by
  have h := hg_concy hΓ 3 0
  linarith

theorem row2447 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 3 2 + (-1 : ℝ) * hg Γ 3 1 + (-1 : ℝ) * hg Γ 3 3 := by
  have h := hg_concy hΓ 3 1
  linarith

theorem row2448 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 3 3 + (-1 : ℝ) * hg Γ 3 2 + (-1 : ℝ) * hg Γ 3 4 := by
  have h := hg_concy hΓ 3 2
  linarith

theorem row2449 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 4 4 + (-1 : ℝ) * hg Γ 3 4 + (-1 : ℝ) * hg Γ 5 4 := by
  have h := hg_concx hΓ 3 4
  linarith

theorem row2450 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 4 5 + (-1 : ℝ) * hg Γ 3 5 + (-1 : ℝ) * hg Γ 5 5 := by
  have h := hg_concx hΓ 3 5
  linarith

theorem row2451 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 4 6 + (-1 : ℝ) * hg Γ 3 6 + (-1 : ℝ) * hg Γ 5 6 := by
  have h := hg_concx hΓ 3 6
  linarith

theorem row2452 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 4 7 + (-1 : ℝ) * hg Γ 3 7 + (-1 : ℝ) * hg Γ 5 7 := by
  have h := hg_concx hΓ 3 7
  linarith

theorem row2453 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 4 8 + (-1 : ℝ) * hg Γ 3 8 + (-1 : ℝ) * hg Γ 5 8 := by
  have h := hg_concx hΓ 3 8
  linarith

theorem row2454 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 4 9 + (-1 : ℝ) * hg Γ 3 9 + (-1 : ℝ) * hg Γ 5 9 := by
  have h := hg_concx hΓ 3 9
  linarith

theorem row2455 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 4 10 + (-1 : ℝ) * hg Γ 3 10 + (-1 : ℝ) * hg Γ 5 10 := by
  have h := hg_concx hΓ 3 10
  linarith

theorem row2456 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 4 11 + (-1 : ℝ) * hg Γ 3 11 + (-1 : ℝ) * hg Γ 5 11 := by
  have h := hg_concx hΓ 3 11
  linarith

theorem row2457 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 4 12 + (-1 : ℝ) * hg Γ 3 12 + (-1 : ℝ) * hg Γ 5 12 := by
  have h := hg_concx hΓ 3 12
  linarith

theorem row2458 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 4 1 + (-1 : ℝ) * hg Γ 4 0 + (-1 : ℝ) * hg Γ 4 2 := by
  have h := hg_concy hΓ 4 0
  linarith

theorem row2459 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * hg Γ 5 0 + (1 : ℝ) * hg Γ 4 1 + (-1 : ℝ) * hg Γ 4 0 + (-1 : ℝ) * Real.log #Γ := by
  have h := hg_link hΓ hinj 4 0
  linarith

theorem row2460 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 4 2 + (-1 : ℝ) * hg Γ 4 1 + (-1 : ℝ) * hg Γ 4 3 := by
  have h := hg_concy hΓ 4 1
  linarith

theorem row2461 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 4 3 + (-1 : ℝ) * hg Γ 4 2 + (-1 : ℝ) * hg Γ 4 4 := by
  have h := hg_concy hΓ 4 2
  linarith

theorem row2462 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 5 5 + (-1 : ℝ) * hg Γ 4 5 + (-1 : ℝ) * hg Γ 6 5 := by
  have h := hg_concx hΓ 4 5
  linarith

theorem row2463 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 5 6 + (-1 : ℝ) * hg Γ 4 6 + (-1 : ℝ) * hg Γ 6 6 := by
  have h := hg_concx hΓ 4 6
  linarith

theorem row2464 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 5 7 + (-1 : ℝ) * hg Γ 4 7 + (-1 : ℝ) * hg Γ 6 7 := by
  have h := hg_concx hΓ 4 7
  linarith

theorem row2465 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 5 8 + (-1 : ℝ) * hg Γ 4 8 + (-1 : ℝ) * hg Γ 6 8 := by
  have h := hg_concx hΓ 4 8
  linarith

theorem row2466 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 5 9 + (-1 : ℝ) * hg Γ 4 9 + (-1 : ℝ) * hg Γ 6 9 := by
  have h := hg_concx hΓ 4 9
  linarith

theorem row2467 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 5 10 + (-1 : ℝ) * hg Γ 4 10 + (-1 : ℝ) * hg Γ 6 10 := by
  have h := hg_concx hΓ 4 10
  linarith

theorem row2468 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 5 11 + (-1 : ℝ) * hg Γ 4 11 + (-1 : ℝ) * hg Γ 6 11 := by
  have h := hg_concx hΓ 4 11
  linarith

theorem row2469 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 5 12 + (-1 : ℝ) * hg Γ 4 12 + (-1 : ℝ) * hg Γ 6 12 := by
  have h := hg_concx hΓ 4 12
  linarith

theorem row2470 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 5 1 + (-1 : ℝ) * hg Γ 5 0 + (-1 : ℝ) * hg Γ 5 2 := by
  have h := hg_concy hΓ 5 0
  linarith

theorem row2471 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * hg Γ 6 0 + (1 : ℝ) * hg Γ 5 1 + (-1 : ℝ) * hg Γ 5 0 + (-1 : ℝ) * Real.log #Γ := by
  have h := hg_link hΓ hinj 5 0
  linarith

theorem row2472 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 5 2 + (-1 : ℝ) * hg Γ 5 1 + (-1 : ℝ) * hg Γ 5 3 := by
  have h := hg_concy hΓ 5 1
  linarith

theorem row2473 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 5 3 + (-1 : ℝ) * hg Γ 5 2 + (-1 : ℝ) * hg Γ 5 4 := by
  have h := hg_concy hΓ 5 2
  linarith

theorem row2474 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 5 4 + (-1 : ℝ) * hg Γ 5 3 + (-1 : ℝ) * hg Γ 5 5 := by
  have h := hg_concy hΓ 5 3
  linarith

theorem row2475 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 6 6 + (-1 : ℝ) * hg Γ 5 6 + (-1 : ℝ) * hg Γ 7 6 := by
  have h := hg_concx hΓ 5 6
  linarith

theorem row2476 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 6 7 + (-1 : ℝ) * hg Γ 5 7 + (-1 : ℝ) * hg Γ 7 7 := by
  have h := hg_concx hΓ 5 7
  linarith

theorem row2477 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 6 8 + (-1 : ℝ) * hg Γ 5 8 + (-1 : ℝ) * hg Γ 7 8 := by
  have h := hg_concx hΓ 5 8
  linarith

theorem row2478 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 6 9 + (-1 : ℝ) * hg Γ 5 9 + (-1 : ℝ) * hg Γ 7 9 := by
  have h := hg_concx hΓ 5 9
  linarith

theorem row2479 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 6 10 + (-1 : ℝ) * hg Γ 5 10 + (-1 : ℝ) * hg Γ 7 10 := by
  have h := hg_concx hΓ 5 10
  linarith

theorem row2480 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 6 11 + (-1 : ℝ) * hg Γ 5 11 + (-1 : ℝ) * hg Γ 7 11 := by
  have h := hg_concx hΓ 5 11
  linarith

theorem row2481 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 6 12 + (-1 : ℝ) * hg Γ 5 12 + (-1 : ℝ) * hg Γ 7 12 := by
  have h := hg_concx hΓ 5 12
  linarith

theorem row2482 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 6 1 + (-1 : ℝ) * hg Γ 6 0 + (-1 : ℝ) * hg Γ 6 2 := by
  have h := hg_concy hΓ 6 0
  linarith

theorem row2483 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * hg Γ 7 0 + (1 : ℝ) * hg Γ 6 1 + (-1 : ℝ) * hg Γ 6 0 + (-1 : ℝ) * Real.log #Γ := by
  have h := hg_link hΓ hinj 6 0
  linarith

theorem row2484 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 6 2 + (-1 : ℝ) * hg Γ 6 1 + (-1 : ℝ) * hg Γ 6 3 := by
  have h := hg_concy hΓ 6 1
  linarith

theorem row2485 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 6 3 + (-1 : ℝ) * hg Γ 6 2 + (-1 : ℝ) * hg Γ 6 4 := by
  have h := hg_concy hΓ 6 2
  linarith

theorem row2486 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 6 4 + (-1 : ℝ) * hg Γ 6 3 + (-1 : ℝ) * hg Γ 6 5 := by
  have h := hg_concy hΓ 6 3
  linarith

theorem row2487 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 6 5 + (-1 : ℝ) * hg Γ 6 4 + (-1 : ℝ) * hg Γ 6 6 := by
  have h := hg_concy hΓ 6 4
  linarith

theorem row2488 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 7 7 + (-1 : ℝ) * hg Γ 6 7 + (-1 : ℝ) * hg Γ 8 7 := by
  have h := hg_concx hΓ 6 7
  linarith

theorem row2489 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 7 8 + (-1 : ℝ) * hg Γ 6 8 + (-1 : ℝ) * hg Γ 8 8 := by
  have h := hg_concx hΓ 6 8
  linarith

theorem row2490 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 7 9 + (-1 : ℝ) * hg Γ 6 9 + (-1 : ℝ) * hg Γ 8 9 := by
  have h := hg_concx hΓ 6 9
  linarith

theorem row2491 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 7 10 + (-1 : ℝ) * hg Γ 6 10 + (-1 : ℝ) * hg Γ 8 10 := by
  have h := hg_concx hΓ 6 10
  linarith

theorem row2492 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 7 11 + (-1 : ℝ) * hg Γ 6 11 + (-1 : ℝ) * hg Γ 8 11 := by
  have h := hg_concx hΓ 6 11
  linarith

theorem row2493 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 7 12 + (-1 : ℝ) * hg Γ 6 12 + (-1 : ℝ) * hg Γ 8 12 := by
  have h := hg_concx hΓ 6 12
  linarith

theorem row2494 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 7 1 + (-1 : ℝ) * hg Γ 7 0 + (-1 : ℝ) * hg Γ 7 2 := by
  have h := hg_concy hΓ 7 0
  linarith

theorem row2495 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * hg Γ 8 0 + (1 : ℝ) * hg Γ 7 1 + (-1 : ℝ) * hg Γ 7 0 + (-1 : ℝ) * Real.log #Γ := by
  have h := hg_link hΓ hinj 7 0
  linarith

theorem row2496 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 7 2 + (-1 : ℝ) * hg Γ 7 1 + (-1 : ℝ) * hg Γ 7 3 := by
  have h := hg_concy hΓ 7 1
  linarith

theorem row2497 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 7 3 + (-1 : ℝ) * hg Γ 7 2 + (-1 : ℝ) * hg Γ 7 4 := by
  have h := hg_concy hΓ 7 2
  linarith

theorem row2498 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 7 4 + (-1 : ℝ) * hg Γ 7 3 + (-1 : ℝ) * hg Γ 7 5 := by
  have h := hg_concy hΓ 7 3
  linarith

theorem row2499 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 7 5 + (-1 : ℝ) * hg Γ 7 4 + (-1 : ℝ) * hg Γ 7 6 := by
  have h := hg_concy hΓ 7 4
  linarith

theorem row2500 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 7 6 + (-1 : ℝ) * hg Γ 7 5 + (-1 : ℝ) * hg Γ 7 7 := by
  have h := hg_concy hΓ 7 5
  linarith

theorem row2501 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 8 8 + (-1 : ℝ) * hg Γ 7 8 + (-1 : ℝ) * hg Γ 9 8 := by
  have h := hg_concx hΓ 7 8
  linarith

theorem row2502 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 8 9 + (-1 : ℝ) * hg Γ 7 9 + (-1 : ℝ) * hg Γ 9 9 := by
  have h := hg_concx hΓ 7 9
  linarith

theorem row2503 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 8 10 + (-1 : ℝ) * hg Γ 7 10 + (-1 : ℝ) * hg Γ 9 10 := by
  have h := hg_concx hΓ 7 10
  linarith

theorem row2504 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * hg Γ 8 11 + (-1 : ℝ) * hg Γ 7 11 := by
  have h := hg_monox hΓ 7 11
  linarith

theorem row2505 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 8 11 + (-1 : ℝ) * hg Γ 7 11 + (-1 : ℝ) * hg Γ 9 11 := by
  have h := hg_concx hΓ 7 11
  linarith

theorem row2506 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 8 12 + (-1 : ℝ) * hg Γ 7 12 + (-1 : ℝ) * hg Γ 9 12 := by
  have h := hg_concx hΓ 7 12
  linarith

theorem row2507 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 8 1 + (-1 : ℝ) * hg Γ 8 0 + (-1 : ℝ) * hg Γ 8 2 := by
  have h := hg_concy hΓ 8 0
  linarith

theorem row2508 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * hg Γ 9 0 + (1 : ℝ) * hg Γ 8 1 + (-1 : ℝ) * hg Γ 8 0 + (-1 : ℝ) * Real.log #Γ := by
  have h := hg_link hΓ hinj 8 0
  linarith

theorem row2509 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 8 2 + (-1 : ℝ) * hg Γ 8 1 + (-1 : ℝ) * hg Γ 8 3 := by
  have h := hg_concy hΓ 8 1
  linarith

theorem row2510 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 8 3 + (-1 : ℝ) * hg Γ 8 2 + (-1 : ℝ) * hg Γ 8 4 := by
  have h := hg_concy hΓ 8 2
  linarith

theorem row2511 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 8 4 + (-1 : ℝ) * hg Γ 8 3 + (-1 : ℝ) * hg Γ 8 5 := by
  have h := hg_concy hΓ 8 3
  linarith

theorem row2512 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 8 5 + (-1 : ℝ) * hg Γ 8 4 + (-1 : ℝ) * hg Γ 8 6 := by
  have h := hg_concy hΓ 8 4
  linarith

theorem row2513 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 8 6 + (-1 : ℝ) * hg Γ 8 5 + (-1 : ℝ) * hg Γ 8 7 := by
  have h := hg_concy hΓ 8 5
  linarith

theorem row2514 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 8 7 + (-1 : ℝ) * hg Γ 8 6 + (-1 : ℝ) * hg Γ 8 8 := by
  have h := hg_concy hΓ 8 6
  linarith

theorem row2515 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 8 8 + (-1 : ℝ) * hg Γ 8 7 + (-1 : ℝ) * hg Γ 8 9 := by
  have h := hg_concy hΓ 8 7
  linarith

theorem row2516 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 9 9 + (-1 : ℝ) * hg Γ 8 9 + (-1 : ℝ) * hg Γ 10 9 := by
  have h := hg_concx hΓ 8 9
  linarith

theorem row2517 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 9 10 + (-1 : ℝ) * hg Γ 8 10 + (-1 : ℝ) * hg Γ 10 10 := by
  have h := hg_concx hΓ 8 10
  linarith

theorem row2518 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 9 11 + (-1 : ℝ) * hg Γ 8 11 + (-1 : ℝ) * hg Γ 10 11 := by
  have h := hg_concx hΓ 8 11
  linarith

theorem row2519 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 9 12 + (-1 : ℝ) * hg Γ 8 12 + (-1 : ℝ) * hg Γ 10 12 := by
  have h := hg_concx hΓ 8 12
  linarith

theorem row2520 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * hg Γ 10 0 + (1 : ℝ) * hg Γ 9 1 + (-1 : ℝ) * hg Γ 9 0 + (-1 : ℝ) * Real.log #Γ := by
  have h := hg_link hΓ hinj 9 0
  linarith

theorem row2521 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 9 2 + (-1 : ℝ) * hg Γ 9 1 + (-1 : ℝ) * hg Γ 9 3 := by
  have h := hg_concy hΓ 9 1
  linarith

theorem row2522 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 9 3 + (-1 : ℝ) * hg Γ 9 2 + (-1 : ℝ) * hg Γ 9 4 := by
  have h := hg_concy hΓ 9 2
  linarith

theorem row2523 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 9 4 + (-1 : ℝ) * hg Γ 9 3 + (-1 : ℝ) * hg Γ 9 5 := by
  have h := hg_concy hΓ 9 3
  linarith

theorem row2524 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 9 5 + (-1 : ℝ) * hg Γ 9 4 + (-1 : ℝ) * hg Γ 9 6 := by
  have h := hg_concy hΓ 9 4
  linarith

theorem row2525 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 9 6 + (-1 : ℝ) * hg Γ 9 5 + (-1 : ℝ) * hg Γ 9 7 := by
  have h := hg_concy hΓ 9 5
  linarith

theorem row2526 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 9 7 + (-1 : ℝ) * hg Γ 9 6 + (-1 : ℝ) * hg Γ 9 8 := by
  have h := hg_concy hΓ 9 6
  linarith

theorem row2527 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 9 8 + (-1 : ℝ) * hg Γ 9 7 + (-1 : ℝ) * hg Γ 9 9 := by
  have h := hg_concy hΓ 9 7
  linarith

theorem row2528 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 10 10 + (-1 : ℝ) * hg Γ 9 10 + (-1 : ℝ) * hg Γ 11 10 := by
  have h := hg_concx hΓ 9 10
  linarith

theorem row2529 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 10 11 + (-1 : ℝ) * hg Γ 9 11 + (-1 : ℝ) * hg Γ 11 11 := by
  have h := hg_concx hΓ 9 11
  linarith

theorem row2530 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 10 12 + (-1 : ℝ) * hg Γ 9 12 + (-1 : ℝ) * hg Γ 11 12 := by
  have h := hg_concx hΓ 9 12
  linarith

theorem row2531 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * hg Γ 11 0 + (1 : ℝ) * hg Γ 10 1 + (-1 : ℝ) * hg Γ 10 0 + (-1 : ℝ) * Real.log #Γ := by
  have h := hg_link hΓ hinj 10 0
  linarith

theorem row2532 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 10 2 + (-1 : ℝ) * hg Γ 10 1 + (-1 : ℝ) * hg Γ 10 3 := by
  have h := hg_concy hΓ 10 1
  linarith

theorem row2533 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 10 3 + (-1 : ℝ) * hg Γ 10 2 + (-1 : ℝ) * hg Γ 10 4 := by
  have h := hg_concy hΓ 10 2
  linarith

theorem row2534 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 10 4 + (-1 : ℝ) * hg Γ 10 3 + (-1 : ℝ) * hg Γ 10 5 := by
  have h := hg_concy hΓ 10 3
  linarith

theorem row2535 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 10 5 + (-1 : ℝ) * hg Γ 10 4 + (-1 : ℝ) * hg Γ 10 6 := by
  have h := hg_concy hΓ 10 4
  linarith

theorem row2536 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 10 6 + (-1 : ℝ) * hg Γ 10 5 + (-1 : ℝ) * hg Γ 10 7 := by
  have h := hg_concy hΓ 10 5
  linarith

theorem row2537 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 10 7 + (-1 : ℝ) * hg Γ 10 6 + (-1 : ℝ) * hg Γ 10 8 := by
  have h := hg_concy hΓ 10 6
  linarith

theorem row2538 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 10 8 + (-1 : ℝ) * hg Γ 10 7 + (-1 : ℝ) * hg Γ 10 9 := by
  have h := hg_concy hΓ 10 7
  linarith

theorem row2539 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 10 9 + (-1 : ℝ) * hg Γ 10 8 + (-1 : ℝ) * hg Γ 10 10 := by
  have h := hg_concy hΓ 10 8
  linarith

theorem row2540 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 10 10 + (-1 : ℝ) * hg Γ 10 9 + (-1 : ℝ) * hg Γ 10 11 := by
  have h := hg_concy hΓ 10 9
  linarith

theorem row2541 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 11 12 + (-1 : ℝ) * hg Γ 10 12 + (-1 : ℝ) * hg Γ 12 12 := by
  have h := hg_concx hΓ 10 12
  linarith

theorem row2542 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * hg Γ 12 0 + (1 : ℝ) * hg Γ 11 1 + (-1 : ℝ) * hg Γ 11 0 + (-1 : ℝ) * Real.log #Γ := by
  have h := hg_link hΓ hinj 11 0
  linarith

theorem row2543 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * hg Γ 12 1 + (1 : ℝ) * hg Γ 11 2 + (-1 : ℝ) * hg Γ 11 1 + (-1 : ℝ) * Real.log #Γ := by
  have h := hg_link hΓ hinj 11 1
  linarith

theorem row2544 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 11 3 + (-1 : ℝ) * hg Γ 11 2 + (-1 : ℝ) * hg Γ 11 4 := by
  have h := hg_concy hΓ 11 2
  linarith

theorem row2545 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 11 4 + (-1 : ℝ) * hg Γ 11 3 + (-1 : ℝ) * hg Γ 11 5 := by
  have h := hg_concy hΓ 11 3
  linarith

theorem row2546 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 11 5 + (-1 : ℝ) * hg Γ 11 4 + (-1 : ℝ) * hg Γ 11 6 := by
  have h := hg_concy hΓ 11 4
  linarith

theorem row2547 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 11 6 + (-1 : ℝ) * hg Γ 11 5 + (-1 : ℝ) * hg Γ 11 7 := by
  have h := hg_concy hΓ 11 5
  linarith

theorem row2548 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 11 7 + (-1 : ℝ) * hg Γ 11 6 + (-1 : ℝ) * hg Γ 11 8 := by
  have h := hg_concy hΓ 11 6
  linarith

theorem row2549 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (2 : ℝ) * hg Γ 11 8 + (-1 : ℝ) * hg Γ 11 7 + (-1 : ℝ) * hg Γ 11 9 := by
  have h := hg_concy hΓ 11 7
  linarith

end EntropyBounds.TwoSet.Certs.R7A5
