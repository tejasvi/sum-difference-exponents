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

theorem row0 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L0 + (1 : ℝ) * HLm Γ 5 L1 + (-1 : ℝ) * HLm Γ 5 L2 := by
  have h := HLm_submod hΓ [F0] ([] : List (Form 5)) [F1]
  rw [show [F0] ++ ([] : List (Form 5)) ++ [F1] = L2 from rfl, show [F0] ++ ([] : List (Form 5)) = L0 from rfl,
    show ([] : List (Form 5)) ++ [F1] = L1 from rfl] at h
  rw [HLm_nil (m := 5) hΓ] at h
  linarith

theorem row1 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L0 + (1 : ℝ) * HLm Γ 5 L3 + (-1 : ℝ) * HLm Γ 5 L4 := by
  have h := HLm_submod hΓ [F0] ([] : List (Form 5)) [F2]
  rw [show [F0] ++ ([] : List (Form 5)) ++ [F2] = L4 from rfl, show [F0] ++ ([] : List (Form 5)) = L0 from rfl,
    show ([] : List (Form 5)) ++ [F2] = L3 from rfl] at h
  rw [HLm_nil (m := 5) hΓ] at h
  linarith

theorem row2 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L0 + (1 : ℝ) * HLm Γ 5 L5 + (-1 : ℝ) * HLm Γ 5 L6 := by
  have h := HLm_submod hΓ [F0] ([] : List (Form 5)) [F3]
  rw [show [F0] ++ ([] : List (Form 5)) ++ [F3] = L6 from rfl, show [F0] ++ ([] : List (Form 5)) = L0 from rfl,
    show ([] : List (Form 5)) ++ [F3] = L5 from rfl] at h
  rw [HLm_nil (m := 5) hΓ] at h
  linarith

theorem row3 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L0 + (1 : ℝ) * HLm Γ 5 L7 + (-1 : ℝ) * HLm Γ 5 L9 := by
  have h := HLm_submod hΓ [F0] ([] : List (Form 5)) [F4]
  rw [show [F0] ++ ([] : List (Form 5)) ++ [F4] = L10 from rfl, show [F0] ++ ([] : List (Form 5)) = L0 from rfl,
    show ([] : List (Form 5)) ++ [F4] = L8 from rfl] at h
  rw [i1 hinj, i0 hinj, HLm_nil (m := 5) hΓ] at h
  linarith

theorem row4 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L0 + (1 : ℝ) * HLm Γ 5 L11 + (-1 : ℝ) * HLm Γ 5 L12 := by
  have h := HLm_submod hΓ [F0] ([] : List (Form 5)) [F5]
  rw [show [F0] ++ ([] : List (Form 5)) ++ [F5] = L12 from rfl, show [F0] ++ ([] : List (Form 5)) = L0 from rfl,
    show ([] : List (Form 5)) ++ [F5] = L11 from rfl] at h
  rw [HLm_nil (m := 5) hΓ] at h
  linarith

theorem row5 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L0 + (1 : ℝ) * HLm Γ 5 L13 + (-1 : ℝ) * HLm Γ 5 L14 := by
  have h := HLm_submod hΓ [F0] ([] : List (Form 5)) [F6]
  rw [show [F0] ++ ([] : List (Form 5)) ++ [F6] = L14 from rfl, show [F0] ++ ([] : List (Form 5)) = L0 from rfl,
    show ([] : List (Form 5)) ++ [F6] = L13 from rfl] at h
  rw [HLm_nil (m := 5) hΓ] at h
  linarith

theorem row6 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L15 + (1 : ℝ) * HLm Γ 5 L3 + (-1 : ℝ) * HLm Γ 5 L16 := by
  have h := HLm_submod hΓ [F7] ([] : List (Form 5)) [F2]
  rw [show [F7] ++ ([] : List (Form 5)) ++ [F2] = L16 from rfl, show [F7] ++ ([] : List (Form 5)) = L15 from rfl,
    show ([] : List (Form 5)) ++ [F2] = L3 from rfl] at h
  rw [HLm_nil (m := 5) hΓ] at h
  linarith

theorem row7 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L15 + (1 : ℝ) * HLm Γ 5 L7 + (-1 : ℝ) * HLm Γ 5 L17 := by
  have h := HLm_submod hΓ [F7] ([] : List (Form 5)) [F4]
  rw [show [F7] ++ ([] : List (Form 5)) ++ [F4] = L18 from rfl, show [F7] ++ ([] : List (Form 5)) = L15 from rfl,
    show ([] : List (Form 5)) ++ [F4] = L8 from rfl] at h
  rw [i2 hinj, i0 hinj, HLm_nil (m := 5) hΓ] at h
  linarith

theorem row8 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L15 + (1 : ℝ) * HLm Γ 5 L19 + (-1 : ℝ) * HLm Γ 5 L20 := by
  have h := HLm_submod hΓ [F7] ([] : List (Form 5)) [F8]
  rw [show [F7] ++ ([] : List (Form 5)) ++ [F8] = L21 from rfl, show [F7] ++ ([] : List (Form 5)) = L15 from rfl,
    show ([] : List (Form 5)) ++ [F8] = L19 from rfl] at h
  rw [i3 hinj, HLm_nil (m := 5) hΓ] at h
  linarith

theorem row9 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L22 + (1 : ℝ) * HLm Γ 5 L7 + (-1 : ℝ) * HLm Γ 5 L23 := by
  have h := HLm_submod hΓ [F9] ([] : List (Form 5)) [F4]
  rw [show [F9] ++ ([] : List (Form 5)) ++ [F4] = L24 from rfl, show [F9] ++ ([] : List (Form 5)) = L22 from rfl,
    show ([] : List (Form 5)) ++ [F4] = L8 from rfl] at h
  rw [i4 hinj, i0 hinj, HLm_nil (m := 5) hΓ] at h
  linarith

theorem row10 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L22 + (1 : ℝ) * HLm Γ 5 L11 + (-1 : ℝ) * HLm Γ 5 L25 := by
  have h := HLm_submod hΓ [F9] ([] : List (Form 5)) [F5]
  rw [show [F9] ++ ([] : List (Form 5)) ++ [F5] = L25 from rfl, show [F9] ++ ([] : List (Form 5)) = L22 from rfl,
    show ([] : List (Form 5)) ++ [F5] = L11 from rfl] at h
  rw [HLm_nil (m := 5) hΓ] at h
  linarith

theorem row11 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L26 + (1 : ℝ) * HLm Γ 5 L28 + (-1 : ℝ) * HLm Γ 5 L29 := by
  have h := HLm_submod hΓ [F10] ([] : List (Form 5)) [F11]
  rw [show [F10] ++ ([] : List (Form 5)) ++ [F11] = L30 from rfl, show [F10] ++ ([] : List (Form 5)) = L27 from rfl,
    show ([] : List (Form 5)) ++ [F11] = L28 from rfl] at h
  rw [i6 hinj, i5 hinj, HLm_nil (m := 5) hΓ] at h
  linarith

theorem row12 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L31 + (1 : ℝ) * HLm Γ 5 L32 + (-1 : ℝ) * HLm Γ 5 L33 := by
  have h := HLm_submod hΓ [F12] ([] : List (Form 5)) [F13]
  rw [show [F12] ++ ([] : List (Form 5)) ++ [F13] = L33 from rfl, show [F12] ++ ([] : List (Form 5)) = L31 from rfl,
    show ([] : List (Form 5)) ++ [F13] = L32 from rfl] at h
  rw [HLm_nil (m := 5) hΓ] at h
  linarith

theorem row13 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L31 + (1 : ℝ) * HLm Γ 5 L34 + (-1 : ℝ) * HLm Γ 5 L35 := by
  have h := HLm_submod hΓ [F12] ([] : List (Form 5)) [F14]
  rw [show [F12] ++ ([] : List (Form 5)) ++ [F14] = L35 from rfl, show [F12] ++ ([] : List (Form 5)) = L31 from rfl,
    show ([] : List (Form 5)) ++ [F14] = L34 from rfl] at h
  rw [HLm_nil (m := 5) hΓ] at h
  linarith

theorem row14 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L31 + (1 : ℝ) * HLm Γ 5 L36 + (-1 : ℝ) * HLm Γ 5 L37 := by
  have h := HLm_submod hΓ [F12] ([] : List (Form 5)) [F15]
  rw [show [F12] ++ ([] : List (Form 5)) ++ [F15] = L37 from rfl, show [F12] ++ ([] : List (Form 5)) = L31 from rfl,
    show ([] : List (Form 5)) ++ [F15] = L36 from rfl] at h
  rw [HLm_nil (m := 5) hΓ] at h
  linarith

theorem row15 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L38 + (1 : ℝ) * HLm Γ 5 L39 + (-1 : ℝ) * HLm Γ 5 L40 := by
  have h := HLm_submod hΓ [F16] ([] : List (Form 5)) [F17]
  rw [show [F16] ++ ([] : List (Form 5)) ++ [F17] = L41 from rfl, show [F16] ++ ([] : List (Form 5)) = L38 from rfl,
    show ([] : List (Form 5)) ++ [F17] = L39 from rfl] at h
  rw [i7 hinj, HLm_nil (m := 5) hΓ] at h
  linarith

theorem row16 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L38 + (1 : ℝ) * HLm Γ 5 L42 + (-1 : ℝ) * HLm Γ 5 L43 := by
  have h := HLm_submod hΓ [F16] ([] : List (Form 5)) [F18]
  rw [show [F16] ++ ([] : List (Form 5)) ++ [F18] = L44 from rfl, show [F16] ++ ([] : List (Form 5)) = L38 from rfl,
    show ([] : List (Form 5)) ++ [F18] = L42 from rfl] at h
  rw [i8 hinj, HLm_nil (m := 5) hΓ] at h
  linarith

theorem row17 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L38 + (1 : ℝ) * HLm Γ 5 L45 + (-1 : ℝ) * HLm Γ 5 L46 := by
  have h := HLm_submod hΓ [F16] ([] : List (Form 5)) [F19]
  rw [show [F16] ++ ([] : List (Form 5)) ++ [F19] = L47 from rfl, show [F16] ++ ([] : List (Form 5)) = L38 from rfl,
    show ([] : List (Form 5)) ++ [F19] = L45 from rfl] at h
  rw [i9 hinj, HLm_nil (m := 5) hΓ] at h
  linarith

theorem row18 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L38 + (1 : ℝ) * HLm Γ 5 L48 + (-1 : ℝ) * HLm Γ 5 L49 := by
  have h := HLm_submod hΓ [F16] ([] : List (Form 5)) [F20]
  rw [show [F16] ++ ([] : List (Form 5)) ++ [F20] = L50 from rfl, show [F16] ++ ([] : List (Form 5)) = L38 from rfl,
    show ([] : List (Form 5)) ++ [F20] = L48 from rfl] at h
  rw [i10 hinj, HLm_nil (m := 5) hΓ] at h
  linarith

theorem row19 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L51 + (1 : ℝ) * HLm Γ 5 L45 + (-1 : ℝ) * HLm Γ 5 L52 := by
  have h := HLm_submod hΓ [F21] ([] : List (Form 5)) [F19]
  rw [show [F21] ++ ([] : List (Form 5)) ++ [F19] = L52 from rfl, show [F21] ++ ([] : List (Form 5)) = L51 from rfl,
    show ([] : List (Form 5)) ++ [F19] = L45 from rfl] at h
  rw [HLm_nil (m := 5) hΓ] at h
  linarith

theorem row20 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L53 + (1 : ℝ) * HLm Γ 5 L54 + (-1 : ℝ) * HLm Γ 5 L55 := by
  have h := HLm_submod hΓ [F22] ([] : List (Form 5)) [F23]
  rw [show [F22] ++ ([] : List (Form 5)) ++ [F23] = L55 from rfl, show [F22] ++ ([] : List (Form 5)) = L53 from rfl,
    show ([] : List (Form 5)) ++ [F23] = L54 from rfl] at h
  rw [HLm_nil (m := 5) hΓ] at h
  linarith

theorem row21 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L11 + (1 : ℝ) * HLm Γ 5 L56 + (-1 : ℝ) * HLm Γ 5 L57 := by
  have h := HLm_submod hΓ [F5] ([] : List (Form 5)) [F24]
  rw [show [F5] ++ ([] : List (Form 5)) ++ [F24] = L58 from rfl, show [F5] ++ ([] : List (Form 5)) = L11 from rfl,
    show ([] : List (Form 5)) ++ [F24] = L56 from rfl] at h
  rw [i11 hinj, HLm_nil (m := 5) hΓ] at h
  linarith

theorem row22 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L59 + (1 : ℝ) * HLm Γ 5 L60 + (-1 : ℝ) * HLm Γ 5 L61 := by
  have h := HLm_submod hΓ [F25] ([] : List (Form 5)) [F26]
  rw [show [F25] ++ ([] : List (Form 5)) ++ [F26] = L62 from rfl, show [F25] ++ ([] : List (Form 5)) = L59 from rfl,
    show ([] : List (Form 5)) ++ [F26] = L60 from rfl] at h
  rw [i12 hinj, HLm_nil (m := 5) hΓ] at h
  linarith

theorem row23 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L63 + (1 : ℝ) * HLm Γ 5 L64 + (-1 : ℝ) * HLm Γ 5 L66 := by
  have h := HLm_submod hΓ [F27] ([] : List (Form 5)) [F29]
  rw [show [F27] ++ ([] : List (Form 5)) ++ [F29] = L67 from rfl, show [F27] ++ ([] : List (Form 5)) = L63 from rfl,
    show ([] : List (Form 5)) ++ [F29] = L65 from rfl] at h
  rw [i14 hinj, i13 hinj, HLm_nil (m := 5) hΓ] at h
  linarith

theorem row24 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L68 + (1 : ℝ) * HLm Γ 5 L69 + (-1 : ℝ) * HLm Γ 5 L70 := by
  have h := HLm_submod hΓ [F30] ([] : List (Form 5)) [F31]
  rw [show [F30] ++ ([] : List (Form 5)) ++ [F31] = L71 from rfl, show [F30] ++ ([] : List (Form 5)) = L68 from rfl,
    show ([] : List (Form 5)) ++ [F31] = L69 from rfl] at h
  rw [i15 hinj, HLm_nil (m := 5) hΓ] at h
  linarith

theorem row25 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L72 + (1 : ℝ) * HLm Γ 5 L73 + (-1 : ℝ) * HLm Γ 5 L74 := by
  have h := HLm_submod hΓ [F33] ([] : List (Form 5)) [F34]
  rw [show [F33] ++ ([] : List (Form 5)) ++ [F34] = L75 from rfl, show [F33] ++ ([] : List (Form 5)) = L72 from rfl,
    show ([] : List (Form 5)) ++ [F34] = L73 from rfl] at h
  rw [i16 hinj, HLm_nil (m := 5) hΓ] at h
  linarith

theorem row26 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L76 + (1 : ℝ) * HLm Γ 5 L77 + (-1 : ℝ) * HLm Γ 5 L79 := by
  have h := HLm_submod hΓ [F36] ([] : List (Form 5)) [F38]
  rw [show [F36] ++ ([] : List (Form 5)) ++ [F38] = L80 from rfl, show [F36] ++ ([] : List (Form 5)) = L76 from rfl,
    show ([] : List (Form 5)) ++ [F38] = L78 from rfl] at h
  rw [i18 hinj, i17 hinj, HLm_nil (m := 5) hΓ] at h
  linarith

theorem row27 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L69 + (1 : ℝ) * HLm Γ 5 L81 + (-1 : ℝ) * HLm Γ 5 L82 := by
  have h := HLm_submod hΓ [F31] ([] : List (Form 5)) [F39]
  rw [show [F31] ++ ([] : List (Form 5)) ++ [F39] = L83 from rfl, show [F31] ++ ([] : List (Form 5)) = L69 from rfl,
    show ([] : List (Form 5)) ++ [F39] = L81 from rfl] at h
  rw [i19 hinj, HLm_nil (m := 5) hΓ] at h
  linarith

theorem row28 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L84 + (1 : ℝ) * HLm Γ 5 L85 + (-1 : ℝ) * HLm Γ 5 L86 := by
  have h := HLm_submod hΓ [F40] ([] : List (Form 5)) [F41]
  rw [show [F40] ++ ([] : List (Form 5)) ++ [F41] = L87 from rfl, show [F40] ++ ([] : List (Form 5)) = L84 from rfl,
    show ([] : List (Form 5)) ++ [F41] = L85 from rfl] at h
  rw [i20 hinj, HLm_nil (m := 5) hΓ] at h
  linarith

theorem row29 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L26 + (1 : ℝ) * HLm Γ 5 L12 + (-1 : ℝ) * HLm Γ 5 L89 + (-1 : ℝ) * HLm Γ 5 L0 := by
  have h := HLm_submod hΓ [F7] L0 [F5]
  rw [show [F7] ++ L0 ++ [F5] = L90 from rfl, show [F7] ++ L0 = L88 from rfl,
    show L0 ++ [F5] = L12 from rfl] at h
  rw [i22 hinj, i21 hinj] at h
  linarith

theorem row30 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L26 + (1 : ℝ) * HLm Γ 5 L91 + (-1 : ℝ) * HLm Γ 5 L92 + (-1 : ℝ) * HLm Γ 5 L0 := by
  have h := HLm_submod hΓ [F7] L0 [F43]
  rw [show [F7] ++ L0 ++ [F43] = L93 from rfl, show [F7] ++ L0 = L88 from rfl,
    show L0 ++ [F43] = L91 from rfl] at h
  rw [i23 hinj, i21 hinj] at h
  linarith

theorem row31 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L94 + (1 : ℝ) * HLm Γ 5 L96 + (-1 : ℝ) * HLm Γ 5 L97 + (-1 : ℝ) * HLm Γ 5 L0 := by
  have h := HLm_submod hΓ [F44] L0 [F45]
  rw [show [F44] ++ L0 ++ [F45] = L98 from rfl, show [F44] ++ L0 = L95 from rfl,
    show L0 ++ [F45] = L96 from rfl] at h
  rw [i25 hinj, i24 hinj] at h
  linarith

theorem row32 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L99 + (1 : ℝ) * HLm Γ 5 L96 + (-1 : ℝ) * HLm Γ 5 L101 + (-1 : ℝ) * HLm Γ 5 L0 := by
  have h := HLm_submod hΓ [F46] L0 [F45]
  rw [show [F46] ++ L0 ++ [F45] = L102 from rfl, show [F46] ++ L0 = L100 from rfl,
    show L0 ++ [F45] = L96 from rfl] at h
  rw [i27 hinj, i26 hinj] at h
  linarith

theorem row33 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L103 + (1 : ℝ) * HLm Γ 5 L105 + (-1 : ℝ) * HLm Γ 5 L106 + (-1 : ℝ) * HLm Γ 5 L0 := by
  have h := HLm_submod hΓ [F16] L0 [F23]
  rw [show [F16] ++ L0 ++ [F23] = L107 from rfl, show [F16] ++ L0 = L104 from rfl,
    show L0 ++ [F23] = L105 from rfl] at h
  rw [i29 hinj, i28 hinj] at h
  linarith

theorem row34 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L108 + (1 : ℝ) * HLm Γ 5 L110 + (-1 : ℝ) * HLm Γ 5 L111 + (-1 : ℝ) * HLm Γ 5 L15 := by
  have h := HLm_submod hΓ [F1] L15 [F16]
  rw [show [F1] ++ L15 ++ [F16] = L112 from rfl, show [F1] ++ L15 = L109 from rfl,
    show L15 ++ [F16] = L110 from rfl] at h
  rw [i31 hinj, i30 hinj] at h
  linarith

theorem row35 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L113 + (1 : ℝ) * HLm Γ 5 L114 + (-1 : ℝ) * HLm Γ 5 L115 + (-1 : ℝ) * HLm Γ 5 L15 := by
  have h := HLm_submod hΓ [F47] L15 [F6]
  rw [show [F47] ++ L15 ++ [F6] = L115 from rfl, show [F47] ++ L15 = L113 from rfl,
    show L15 ++ [F6] = L114 from rfl] at h
  linarith

theorem row36 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L110 + (1 : ℝ) * HLm Γ 5 L117 + (-1 : ℝ) * HLm Γ 5 L118 + (-1 : ℝ) * HLm Γ 5 L15 := by
  have h := HLm_submod hΓ [F16] L15 [F23]
  rw [show [F16] ++ L15 ++ [F23] = L119 from rfl, show [F16] ++ L15 = L116 from rfl,
    show L15 ++ [F23] = L117 from rfl] at h
  rw [i33 hinj, i32 hinj] at h
  linarith

theorem row37 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L120 + (1 : ℝ) * HLm Γ 5 L122 + (-1 : ℝ) * HLm Γ 5 L124 + (-1 : ℝ) * HLm Γ 5 L15 := by
  have h := HLm_submod hΓ [F48] L15 [F50]
  rw [show [F48] ++ L15 ++ [F50] = L125 from rfl, show [F48] ++ L15 = L121 from rfl,
    show L15 ++ [F50] = L123 from rfl] at h
  rw [i36 hinj, i34 hinj, i35 hinj] at h
  linarith

theorem row38 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L126 + (1 : ℝ) * HLm Γ 5 L127 + (-1 : ℝ) * HLm Γ 5 L129 + (-1 : ℝ) * HLm Γ 5 L3 := by
  have h := HLm_submod hΓ [F27] L3 [F29]
  rw [show [F27] ++ L3 ++ [F29] = L130 from rfl, show [F27] ++ L3 = L126 from rfl,
    show L3 ++ [F29] = L128 from rfl] at h
  rw [i38 hinj, i37 hinj] at h
  linarith

theorem row39 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L131 + (1 : ℝ) * HLm Γ 5 L133 + (-1 : ℝ) * HLm Γ 5 L134 + (-1 : ℝ) * HLm Γ 5 L136 := by
  have h := HLm_submod hΓ [F46] L136 [F45]
  rw [show [F46] ++ L136 ++ [F45] = L135 from rfl, show [F46] ++ L136 = L132 from rfl,
    show L136 ++ [F45] = L133 from rfl] at h
  rw [i40 hinj, i39 hinj] at h
  linarith

theorem row40 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L137 + (1 : ℝ) * HLm Γ 5 L139 + (-1 : ℝ) * HLm Γ 5 L141 + (-1 : ℝ) * HLm Γ 5 L136 := by
  have h := HLm_submod hΓ [F16] L136 [F52]
  rw [show [F16] ++ L136 ++ [F52] = L142 from rfl, show [F16] ++ L136 = L138 from rfl,
    show L136 ++ [F52] = L140 from rfl] at h
  rw [i43 hinj, i41 hinj, i42 hinj] at h
  linarith

theorem row41 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L113 + (1 : ℝ) * HLm Γ 5 L144 + (-1 : ℝ) * HLm Γ 5 L145 + (-1 : ℝ) * HLm Γ 5 L147 := by
  have h := HLm_submod hΓ [F7] L147 [F48]
  rw [show [F7] ++ L147 ++ [F48] = L146 from rfl, show [F7] ++ L147 = L143 from rfl,
    show L147 ++ [F48] = L144 from rfl] at h
  rw [i45 hinj, i44 hinj] at h
  linarith

theorem row42 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L148 + (1 : ℝ) * HLm Γ 5 L150 + (-1 : ℝ) * HLm Γ 5 L152 + (-1 : ℝ) * HLm Γ 5 L147 := by
  have h := HLm_submod hΓ [F16] L147 [F20]
  rw [show [F16] ++ L147 ++ [F20] = L153 from rfl, show [F16] ++ L147 = L149 from rfl,
    show L147 ++ [F20] = L151 from rfl] at h
  rw [i48 hinj, i46 hinj, i47 hinj] at h
  linarith

theorem row43 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L26 + (1 : ℝ) * HLm Γ 5 L155 + (-1 : ℝ) * HLm Γ 5 L157 + (-1 : ℝ) * HLm Γ 5 L22 := by
  have h := HLm_submod hΓ [F0] L22 [F55]
  rw [show [F0] ++ L22 ++ [F55] = L158 from rfl, show [F0] ++ L22 = L154 from rfl,
    show L22 ++ [F55] = L156 from rfl] at h
  rw [i51 hinj, i49 hinj, i50 hinj] at h
  linarith

theorem row44 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L159 + (1 : ℝ) * HLm Γ 5 L161 + (-1 : ℝ) * HLm Γ 5 L162 + (-1 : ℝ) * HLm Γ 5 L22 := by
  have h := HLm_submod hΓ [F21] L22 [F23]
  rw [show [F21] ++ L22 ++ [F23] = L163 from rfl, show [F21] ++ L22 = L160 from rfl,
    show L22 ++ [F23] = L161 from rfl] at h
  rw [i53 hinj, i52 hinj] at h
  linarith

theorem row45 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L159 + (1 : ℝ) * HLm Γ 5 L164 + (-1 : ℝ) * HLm Γ 5 L166 + (-1 : ℝ) * HLm Γ 5 L22 := by
  have h := HLm_submod hΓ [F21] L22 [F20]
  rw [show [F21] ++ L22 ++ [F20] = L167 from rfl, show [F21] ++ L22 = L160 from rfl,
    show L22 ++ [F20] = L165 from rfl] at h
  rw [i55 hinj, i52 hinj, i54 hinj] at h
  linarith

theorem row46 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L168 + (1 : ℝ) * HLm Γ 5 L161 + (-1 : ℝ) * HLm Γ 5 L170 + (-1 : ℝ) * HLm Γ 5 L22 := by
  have h := HLm_submod hΓ [F22] L22 [F23]
  rw [show [F22] ++ L22 ++ [F23] = L171 from rfl, show [F22] ++ L22 = L169 from rfl,
    show L22 ++ [F23] = L161 from rfl] at h
  rw [i57 hinj, i56 hinj] at h
  linarith

theorem row47 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L172 + (1 : ℝ) * HLm Γ 5 L174 + (-1 : ℝ) * HLm Γ 5 L176 + (-1 : ℝ) * HLm Γ 5 L22 := by
  have h := HLm_submod hΓ [F25] L22 [F26]
  rw [show [F25] ++ L22 ++ [F26] = L177 from rfl, show [F25] ++ L22 = L173 from rfl,
    show L22 ++ [F26] = L175 from rfl] at h
  rw [i60 hinj, i58 hinj, i59 hinj] at h
  linarith

theorem row48 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L178 + (1 : ℝ) * HLm Γ 5 L180 + (-1 : ℝ) * HLm Γ 5 L181 + (-1 : ℝ) * HLm Γ 5 L31 := by
  have h := HLm_submod hΓ [F7] L31 [F16]
  rw [show [F7] ++ L31 ++ [F16] = L182 from rfl, show [F7] ++ L31 = L179 from rfl,
    show L31 ++ [F16] = L180 from rfl] at h
  rw [i62 hinj, i61 hinj] at h
  linarith

theorem row49 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L183 + (1 : ℝ) * HLm Γ 5 L180 + (-1 : ℝ) * HLm Γ 5 L185 + (-1 : ℝ) * HLm Γ 5 L31 := by
  have h := HLm_submod hΓ [F62] L31 [F16]
  rw [show [F62] ++ L31 ++ [F16] = L186 from rfl, show [F62] ++ L31 = L184 from rfl,
    show L31 ++ [F16] = L180 from rfl] at h
  rw [i64 hinj, i63 hinj] at h
  linarith

theorem row50 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L183 + (1 : ℝ) * HLm Γ 5 L187 + (-1 : ℝ) * HLm Γ 5 L188 + (-1 : ℝ) * HLm Γ 5 L31 := by
  have h := HLm_submod hΓ [F62] L31 [F45]
  rw [show [F62] ++ L31 ++ [F45] = L189 from rfl, show [F62] ++ L31 = L184 from rfl,
    show L31 ++ [F45] = L187 from rfl] at h
  rw [i65 hinj, i63 hinj] at h
  linarith

theorem row51 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L183 + (1 : ℝ) * HLm Γ 5 L190 + (-1 : ℝ) * HLm Γ 5 L192 + (-1 : ℝ) * HLm Γ 5 L31 := by
  have h := HLm_submod hΓ [F62] L31 [F6]
  rw [show [F62] ++ L31 ++ [F6] = L193 from rfl, show [F62] ++ L31 = L184 from rfl,
    show L31 ++ [F6] = L191 from rfl] at h
  rw [i67 hinj, i63 hinj, i66 hinj] at h
  linarith

theorem row52 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L194 + (1 : ℝ) * HLm Γ 5 L196 + (-1 : ℝ) * HLm Γ 5 L197 + (-1 : ℝ) * HLm Γ 5 L199 := by
  have h := HLm_submod hΓ [F17] L199 [F45]
  rw [show [F17] ++ L199 ++ [F45] = L198 from rfl, show [F17] ++ L199 = L195 from rfl,
    show L199 ++ [F45] = L196 from rfl] at h
  rw [i69 hinj, i68 hinj] at h
  linarith

theorem row53 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L99 + (1 : ℝ) * HLm Γ 5 L200 + (-1 : ℝ) * HLm Γ 5 L202 + (-1 : ℝ) * HLm Γ 5 L204 := by
  have h := HLm_submod hΓ [F0] L204 [F14]
  rw [show [F0] ++ L204 ++ [F14] = L203 from rfl, show [F0] ++ L204 = L99 from rfl,
    show L204 ++ [F14] = L201 from rfl] at h
  rw [i71 hinj, i70 hinj] at h
  linarith

theorem row54 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L205 + (1 : ℝ) * HLm Γ 5 L206 + (-1 : ℝ) * HLm Γ 5 L208 + (-1 : ℝ) * HLm Γ 5 L204 := by
  have h := HLm_submod hΓ [F47] L204 [F13]
  rw [show [F47] ++ L204 ++ [F13] = L209 from rfl, show [F47] ++ L204 = L205 from rfl,
    show L204 ++ [F13] = L207 from rfl] at h
  rw [i73 hinj, i72 hinj] at h
  linarith

theorem row55 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L210 + (1 : ℝ) * HLm Γ 5 L212 + (-1 : ℝ) * HLm Γ 5 L214 + (-1 : ℝ) * HLm Γ 5 L204 := by
  have h := HLm_submod hΓ [F16] L204 [F66]
  rw [show [F16] ++ L204 ++ [F66] = L215 from rfl, show [F16] ++ L204 = L211 from rfl,
    show L204 ++ [F66] = L213 from rfl] at h
  rw [i76 hinj, i74 hinj, i75 hinj] at h
  linarith

theorem row56 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L216 + (1 : ℝ) * HLm Γ 5 L217 + (-1 : ℝ) * HLm Γ 5 L218 + (-1 : ℝ) * HLm Γ 5 L38 := by
  have h := HLm_submod hΓ [F44] L38 [F67]
  rw [show [F44] ++ L38 ++ [F67] = L218 from rfl, show [F44] ++ L38 = L216 from rfl,
    show L38 ++ [F67] = L217 from rfl] at h
  linarith

theorem row57 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L217 + (1 : ℝ) * HLm Γ 5 L40 + (-1 : ℝ) * HLm Γ 5 L220 + (-1 : ℝ) * HLm Γ 5 L38 := by
  have h := HLm_submod hΓ [F67] L38 [F17]
  rw [show [F67] ++ L38 ++ [F17] = L221 from rfl, show [F67] ++ L38 = L219 from rfl,
    show L38 ++ [F17] = L41 from rfl] at h
  rw [i78 hinj, i77 hinj, i7 hinj] at h
  linarith

theorem row58 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L222 + (1 : ℝ) * HLm Γ 5 L224 + (-1 : ℝ) * HLm Γ 5 L225 + (-1 : ℝ) * HLm Γ 5 L51 := by
  have h := HLm_submod hΓ [F4] L51 [F13]
  rw [show [F4] ++ L51 ++ [F13] = L226 from rfl, show [F4] ++ L51 = L223 from rfl,
    show L51 ++ [F13] = L224 from rfl] at h
  rw [i80 hinj, i79 hinj] at h
  linarith

theorem row59 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L227 + (1 : ℝ) * HLm Γ 5 L229 + (-1 : ℝ) * HLm Γ 5 L231 + (-1 : ℝ) * HLm Γ 5 L51 := by
  have h := HLm_submod hΓ [F68] L51 [F59]
  rw [show [F68] ++ L51 ++ [F59] = L232 from rfl, show [F68] ++ L51 = L228 from rfl,
    show L51 ++ [F59] = L230 from rfl] at h
  rw [i83 hinj, i81 hinj, i82 hinj] at h
  linarith

theorem row60 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L233 + (1 : ℝ) * HLm Γ 5 L234 + (-1 : ℝ) * HLm Γ 5 L235 + (-1 : ℝ) * HLm Γ 5 L53 := by
  have h := HLm_submod hΓ [F0] L53 [F3]
  rw [show [F0] ++ L53 ++ [F3] = L235 from rfl, show [F0] ++ L53 = L233 from rfl,
    show L53 ++ [F3] = L234 from rfl] at h
  linarith

theorem row61 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L110 + (1 : ℝ) * HLm Γ 5 L237 + (-1 : ℝ) * HLm Γ 5 L239 + (-1 : ℝ) * HLm Γ 5 L53 := by
  have h := HLm_submod hΓ [F7] L53 [F15]
  rw [show [F7] ++ L53 ++ [F15] = L240 from rfl, show [F7] ++ L53 = L236 from rfl,
    show L53 ++ [F15] = L238 from rfl] at h
  rw [i86 hinj, i84 hinj, i85 hinj] at h
  linarith

theorem row62 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L241 + (1 : ℝ) * HLm Γ 5 L243 + (-1 : ℝ) * HLm Γ 5 L245 + (-1 : ℝ) * HLm Γ 5 L53 := by
  have h := HLm_submod hΓ [F67] L53 [F25]
  rw [show [F67] ++ L53 ++ [F25] = L246 from rfl, show [F67] ++ L53 = L242 from rfl,
    show L53 ++ [F25] = L244 from rfl] at h
  rw [i89 hinj, i87 hinj, i88 hinj] at h
  linarith

theorem row63 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L247 + (1 : ℝ) * HLm Γ 5 L248 + (-1 : ℝ) * HLm Γ 5 L250 + (-1 : ℝ) * HLm Γ 5 L53 := by
  have h := HLm_submod hΓ [F30] L53 [F31]
  rw [show [F30] ++ L53 ++ [F31] = L251 from rfl, show [F30] ++ L53 = L247 from rfl,
    show L53 ++ [F31] = L249 from rfl] at h
  rw [i91 hinj, i90 hinj] at h
  linarith

theorem row64 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L252 + (1 : ℝ) * HLm Γ 5 L254 + (-1 : ℝ) * HLm Γ 5 L256 + (-1 : ℝ) * HLm Γ 5 L39 := by
  have h := HLm_submod hΓ [F0] L39 [F72]
  rw [show [F0] ++ L39 ++ [F72] = L257 from rfl, show [F0] ++ L39 = L253 from rfl,
    show L39 ++ [F72] = L255 from rfl] at h
  rw [i94 hinj, i92 hinj, i93 hinj] at h
  linarith

theorem row65 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L258 + (1 : ℝ) * HLm Γ 5 L40 + (-1 : ℝ) * HLm Γ 5 L260 + (-1 : ℝ) * HLm Γ 5 L39 := by
  have h := HLm_submod hΓ [F1] L39 [F16]
  rw [show [F1] ++ L39 ++ [F16] = L261 from rfl, show [F1] ++ L39 = L259 from rfl,
    show L39 ++ [F16] = L40 from rfl] at h
  rw [i96 hinj, i95 hinj] at h
  linarith

theorem row66 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L113 + (1 : ℝ) * HLm Γ 5 L40 + (-1 : ℝ) * HLm Γ 5 L263 + (-1 : ℝ) * HLm Γ 5 L39 := by
  have h := HLm_submod hΓ [F7] L39 [F16]
  rw [show [F7] ++ L39 ++ [F16] = L264 from rfl, show [F7] ++ L39 = L262 from rfl,
    show L39 ++ [F16] = L40 from rfl] at h
  rw [i98 hinj, i97 hinj] at h
  linarith

theorem row67 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L265 + (1 : ℝ) * HLm Γ 5 L267 + (-1 : ℝ) * HLm Γ 5 L269 + (-1 : ℝ) * HLm Γ 5 L39 := by
  have h := HLm_submod hΓ [F2] L39 [F13]
  rw [show [F2] ++ L39 ++ [F13] = L270 from rfl, show [F2] ++ L39 = L266 from rfl,
    show L39 ++ [F13] = L268 from rfl] at h
  rw [i101 hinj, i99 hinj, i100 hinj] at h
  linarith

theorem row68 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L271 + (1 : ℝ) * HLm Γ 5 L273 + (-1 : ℝ) * HLm Γ 5 L274 + (-1 : ℝ) * HLm Γ 5 L39 := by
  have h := HLm_submod hΓ [F9] L39 [F45]
  rw [show [F9] ++ L39 ++ [F45] = L275 from rfl, show [F9] ++ L39 = L272 from rfl,
    show L39 ++ [F45] = L273 from rfl] at h
  rw [i103 hinj, i102 hinj] at h
  linarith

theorem row69 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L276 + (1 : ℝ) * HLm Γ 5 L40 + (-1 : ℝ) * HLm Γ 5 L278 + (-1 : ℝ) * HLm Γ 5 L39 := by
  have h := HLm_submod hΓ [F12] L39 [F16]
  rw [show [F12] ++ L39 ++ [F16] = L279 from rfl, show [F12] ++ L39 = L277 from rfl,
    show L39 ++ [F16] = L40 from rfl] at h
  rw [i105 hinj, i104 hinj] at h
  linarith

theorem row70 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L280 + (1 : ℝ) * HLm Γ 5 L40 + (-1 : ℝ) * HLm Γ 5 L282 + (-1 : ℝ) * HLm Γ 5 L39 := by
  have h := HLm_submod hΓ [F3] L39 [F16]
  rw [show [F3] ++ L39 ++ [F16] = L283 from rfl, show [F3] ++ L39 = L281 from rfl,
    show L39 ++ [F16] = L40 from rfl] at h
  rw [i107 hinj, i106 hinj] at h
  linarith

theorem row71 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L40 + (1 : ℝ) * HLm Γ 5 L284 + (-1 : ℝ) * HLm Γ 5 L286 + (-1 : ℝ) * HLm Γ 5 L39 := by
  have h := HLm_submod hΓ [F16] L39 [F68]
  rw [show [F16] ++ L39 ++ [F68] = L287 from rfl, show [F16] ++ L39 = L41 from rfl,
    show L39 ++ [F68] = L285 from rfl] at h
  rw [i109 hinj, i7 hinj, i108 hinj] at h
  linarith

theorem row72 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L288 + (1 : ℝ) * HLm Γ 5 L289 + (-1 : ℝ) * HLm Γ 5 L291 + (-1 : ℝ) * HLm Γ 5 L59 := by
  have h := HLm_submod hΓ [F0] L59 [F15]
  rw [show [F0] ++ L59 ++ [F15] = L292 from rfl, show [F0] ++ L59 = L288 from rfl,
    show L59 ++ [F15] = L290 from rfl] at h
  rw [i111 hinj, i110 hinj] at h
  linarith

theorem row73 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L233 + (1 : ℝ) * HLm Γ 5 L294 + (-1 : ℝ) * HLm Γ 5 L295 + (-1 : ℝ) * HLm Γ 5 L63 := by
  have h := HLm_submod hΓ [F0] L63 [F23]
  rw [show [F0] ++ L63 ++ [F23] = L296 from rfl, show [F0] ++ L63 = L293 from rfl,
    show L63 ++ [F23] = L294 from rfl] at h
  rw [i113 hinj, i112 hinj] at h
  linarith

theorem row74 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L297 + (1 : ℝ) * HLm Γ 5 L299 + (-1 : ℝ) * HLm Γ 5 L301 + (-1 : ℝ) * HLm Γ 5 L63 := by
  have h := HLm_submod hΓ [F1] L63 [F26]
  rw [show [F1] ++ L63 ++ [F26] = L302 from rfl, show [F1] ++ L63 = L298 from rfl,
    show L63 ++ [F26] = L300 from rfl] at h
  rw [i116 hinj, i114 hinj, i115 hinj] at h
  linarith

theorem row75 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L303 + (1 : ℝ) * HLm Γ 5 L294 + (-1 : ℝ) * HLm Γ 5 L305 + (-1 : ℝ) * HLm Γ 5 L63 := by
  have h := HLm_submod hΓ [F7] L63 [F23]
  rw [show [F7] ++ L63 ++ [F23] = L306 from rfl, show [F7] ++ L63 = L304 from rfl,
    show L63 ++ [F23] = L294 from rfl] at h
  rw [i118 hinj, i117 hinj] at h
  linarith

theorem row76 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L307 + (1 : ℝ) * HLm Γ 5 L309 + (-1 : ℝ) * HLm Γ 5 L310 + (-1 : ℝ) * HLm Γ 5 L63 := by
  have h := HLm_submod hΓ [F9] L63 [F82]
  rw [show [F9] ++ L63 ++ [F82] = L311 from rfl, show [F9] ++ L63 = L308 from rfl,
    show L63 ++ [F82] = L309 from rfl] at h
  rw [i120 hinj, i119 hinj] at h
  linarith

theorem row77 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L312 + (1 : ℝ) * HLm Γ 5 L314 + (-1 : ℝ) * HLm Γ 5 L316 + (-1 : ℝ) * HLm Γ 5 L63 := by
  have h := HLm_submod hΓ [F3] L63 [F45]
  rw [show [F3] ++ L63 ++ [F45] = L317 from rfl, show [F3] ++ L63 = L313 from rfl,
    show L63 ++ [F45] = L315 from rfl] at h
  rw [i123 hinj, i121 hinj, i122 hinj] at h
  linarith

theorem row78 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L318 + (1 : ℝ) * HLm Γ 5 L320 + (-1 : ℝ) * HLm Γ 5 L321 + (-1 : ℝ) * HLm Γ 5 L63 := by
  have h := HLm_submod hΓ [F46] L63 [F67]
  rw [show [F46] ++ L63 ++ [F67] = L322 from rfl, show [F46] ++ L63 = L319 from rfl,
    show L63 ++ [F67] = L320 from rfl] at h
  rw [i125 hinj, i124 hinj] at h
  linarith

theorem row79 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L323 + (1 : ℝ) * HLm Γ 5 L66 + (-1 : ℝ) * HLm Γ 5 L325 + (-1 : ℝ) * HLm Γ 5 L63 := by
  have h := HLm_submod hΓ [F85] L63 [F29]
  rw [show [F85] ++ L63 ++ [F29] = L326 from rfl, show [F85] ++ L63 = L324 from rfl,
    show L63 ++ [F29] = L67 from rfl] at h
  rw [i127 hinj, i126 hinj, i14 hinj] at h
  linarith

theorem row80 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L327 + (1 : ℝ) * HLm Γ 5 L329 + (-1 : ℝ) * HLm Γ 5 L330 + (-1 : ℝ) * HLm Γ 5 L332 := by
  have h := HLm_submod hΓ [F0] L332 [F67]
  rw [show [F0] ++ L332 ++ [F67] = L331 from rfl, show [F0] ++ L332 = L328 from rfl,
    show L332 ++ [F67] = L329 from rfl] at h
  rw [i129 hinj, i128 hinj] at h
  linarith

theorem row81 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L333 + (1 : ℝ) * HLm Γ 5 L329 + (-1 : ℝ) * HLm Γ 5 L335 + (-1 : ℝ) * HLm Γ 5 L332 := by
  have h := HLm_submod hΓ [F1] L332 [F67]
  rw [show [F1] ++ L332 ++ [F67] = L336 from rfl, show [F1] ++ L332 = L334 from rfl,
    show L332 ++ [F67] = L329 from rfl] at h
  rw [i131 hinj, i130 hinj] at h
  linarith

theorem row82 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L157 + (1 : ℝ) * HLm Γ 5 L329 + (-1 : ℝ) * HLm Γ 5 L338 + (-1 : ℝ) * HLm Γ 5 L332 := by
  have h := HLm_submod hΓ [F10] L332 [F67]
  rw [show [F10] ++ L332 ++ [F67] = L339 from rfl, show [F10] ++ L332 = L337 from rfl,
    show L332 ++ [F67] = L329 from rfl] at h
  rw [i133 hinj, i132 hinj] at h
  linarith

theorem row83 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L12 + (1 : ℝ) * HLm Γ 5 L341 + (-1 : ℝ) * HLm Γ 5 L342 + (-1 : ℝ) * HLm Γ 5 L68 := by
  have h := HLm_submod hΓ [F0] L68 [F14]
  rw [show [F0] ++ L68 ++ [F14] = L343 from rfl, show [F0] ++ L68 = L340 from rfl,
    show L68 ++ [F14] = L341 from rfl] at h
  rw [i135 hinj, i134 hinj] at h
  linarith

theorem row84 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L344 + (1 : ℝ) * HLm Γ 5 L346 + (-1 : ℝ) * HLm Γ 5 L347 + (-1 : ℝ) * HLm Γ 5 L68 := by
  have h := HLm_submod hΓ [F1] L68 [F72]
  rw [show [F1] ++ L68 ++ [F72] = L348 from rfl, show [F1] ++ L68 = L345 from rfl,
    show L68 ++ [F72] = L346 from rfl] at h
  rw [i137 hinj, i136 hinj] at h
  linarith

theorem row85 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L349 + (1 : ℝ) * HLm Γ 5 L351 + (-1 : ℝ) * HLm Γ 5 L352 + (-1 : ℝ) * HLm Γ 5 L68 := by
  have h := HLm_submod hΓ [F2] L68 [F15]
  rw [show [F2] ++ L68 ++ [F15] = L353 from rfl, show [F2] ++ L68 = L350 from rfl,
    show L68 ++ [F15] = L351 from rfl] at h
  rw [i139 hinj, i138 hinj] at h
  linarith

theorem row86 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L354 + (1 : ℝ) * HLm Γ 5 L356 + (-1 : ℝ) * HLm Γ 5 L358 + (-1 : ℝ) * HLm Γ 5 L68 := by
  have h := HLm_submod hΓ [F62] L68 [F38]
  rw [show [F62] ++ L68 ++ [F38] = L359 from rfl, show [F62] ++ L68 = L355 from rfl,
    show L68 ++ [F38] = L357 from rfl] at h
  rw [i142 hinj, i140 hinj, i141 hinj] at h
  linarith

theorem row87 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L360 + (1 : ℝ) * HLm Γ 5 L362 + (-1 : ℝ) * HLm Γ 5 L364 + (-1 : ℝ) * HLm Γ 5 L68 := by
  have h := HLm_submod hΓ [F3] L68 [F87]
  rw [show [F3] ++ L68 ++ [F87] = L365 from rfl, show [F3] ++ L68 = L361 from rfl,
    show L68 ++ [F87] = L363 from rfl] at h
  rw [i145 hinj, i143 hinj, i144 hinj] at h
  linarith

theorem row88 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L366 + (1 : ℝ) * HLm Γ 5 L368 + (-1 : ℝ) * HLm Γ 5 L369 + (-1 : ℝ) * HLm Γ 5 L68 := by
  have h := HLm_submod hΓ [F44] L68 [F67]
  rw [show [F44] ++ L68 ++ [F67] = L370 from rfl, show [F44] ++ L68 = L367 from rfl,
    show L68 ++ [F67] = L368 from rfl] at h
  rw [i147 hinj, i146 hinj] at h
  linarith

theorem row89 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L247 + (1 : ℝ) * HLm Γ 5 L368 + (-1 : ℝ) * HLm Γ 5 L372 + (-1 : ℝ) * HLm Γ 5 L68 := by
  have h := HLm_submod hΓ [F22] L68 [F67]
  rw [show [F22] ++ L68 ++ [F67] = L373 from rfl, show [F22] ++ L68 = L371 from rfl,
    show L68 ++ [F67] = L368 from rfl] at h
  rw [i149 hinj, i148 hinj] at h
  linarith

theorem row90 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L247 + (1 : ℝ) * HLm Γ 5 L374 + (-1 : ℝ) * HLm Γ 5 L376 + (-1 : ℝ) * HLm Γ 5 L68 := by
  have h := HLm_submod hΓ [F22] L68 [F29]
  rw [show [F22] ++ L68 ++ [F29] = L377 from rfl, show [F22] ++ L68 = L371 from rfl,
    show L68 ++ [F29] = L375 from rfl] at h
  rw [i151 hinj, i148 hinj, i150 hinj] at h
  linarith

theorem row91 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L368 + (1 : ℝ) * HLm Γ 5 L379 + (-1 : ℝ) * HLm Γ 5 L380 + (-1 : ℝ) * HLm Γ 5 L68 := by
  have h := HLm_submod hΓ [F67] L68 [F88]
  rw [show [F67] ++ L68 ++ [F88] = L381 from rfl, show [F67] ++ L68 = L378 from rfl,
    show L68 ++ [F88] = L379 from rfl] at h
  rw [i153 hinj, i152 hinj] at h
  linarith

theorem row92 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L382 + (1 : ℝ) * HLm Γ 5 L384 + (-1 : ℝ) * HLm Γ 5 L385 + (-1 : ℝ) * HLm Γ 5 L387 := by
  have h := HLm_submod hΓ [F9] L387 [F67]
  rw [show [F9] ++ L387 ++ [F67] = L386 from rfl, show [F9] ++ L387 = L383 from rfl,
    show L387 ++ [F67] = L384 from rfl] at h
  rw [i155 hinj, i154 hinj] at h
  linarith

theorem row93 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L388 + (1 : ℝ) * HLm Γ 5 L390 + (-1 : ℝ) * HLm Γ 5 L391 + (-1 : ℝ) * HLm Γ 5 L72 := by
  have h := HLm_submod hΓ [F2] L72 [F67]
  rw [show [F2] ++ L72 ++ [F67] = L392 from rfl, show [F2] ++ L72 = L389 from rfl,
    show L72 ++ [F67] = L390 from rfl] at h
  rw [i157 hinj, i156 hinj] at h
  linarith

theorem row94 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L393 + (1 : ℝ) * HLm Γ 5 L394 + (-1 : ℝ) * HLm Γ 5 L396 + (-1 : ℝ) * HLm Γ 5 L73 := by
  have h := HLm_submod hΓ [F0] L73 [F6]
  rw [show [F0] ++ L73 ++ [F6] = L397 from rfl, show [F0] ++ L73 = L393 from rfl,
    show L73 ++ [F6] = L395 from rfl] at h
  rw [i159 hinj, i158 hinj] at h
  linarith

theorem row95 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L398 + (1 : ℝ) * HLm Γ 5 L400 + (-1 : ℝ) * HLm Γ 5 L402 + (-1 : ℝ) * HLm Γ 5 L73 := by
  have h := HLm_submod hΓ [F16] L73 [F52]
  rw [show [F16] ++ L73 ++ [F52] = L403 from rfl, show [F16] ++ L73 = L399 from rfl,
    show L73 ++ [F52] = L401 from rfl] at h
  rw [i162 hinj, i160 hinj, i161 hinj] at h
  linarith

theorem row96 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L404 + (1 : ℝ) * HLm Γ 5 L406 + (-1 : ℝ) * HLm Γ 5 L408 + (-1 : ℝ) * HLm Γ 5 L73 := by
  have h := HLm_submod hΓ [F17] L73 [F13]
  rw [show [F17] ++ L73 ++ [F13] = L409 from rfl, show [F17] ++ L73 = L405 from rfl,
    show L73 ++ [F13] = L407 from rfl] at h
  rw [i165 hinj, i163 hinj, i164 hinj] at h
  linarith

theorem row97 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L79 + (1 : ℝ) * HLm Γ 5 L411 + (-1 : ℝ) * HLm Γ 5 L413 + (-1 : ℝ) * HLm Γ 5 L76 := by
  have h := HLm_submod hΓ [F38] L76 [F88]
  rw [show [F38] ++ L76 ++ [F88] = L414 from rfl, show [F38] ++ L76 = L410 from rfl,
    show L76 ++ [F88] = L412 from rfl] at h
  rw [i168 hinj, i166 hinj, i167 hinj] at h
  linarith

theorem row98 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L415 + (1 : ℝ) * HLm Γ 5 L417 + (-1 : ℝ) * HLm Γ 5 L418 + (-1 : ℝ) * HLm Γ 5 L420 := by
  have h := HLm_submod hΓ [F16] L420 [F67]
  rw [show [F16] ++ L420 ++ [F67] = L419 from rfl, show [F16] ++ L420 = L416 from rfl,
    show L420 ++ [F67] = L417 from rfl] at h
  rw [i170 hinj, i169 hinj] at h
  linarith

theorem row99 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L421 + (1 : ℝ) * HLm Γ 5 L423 + (-1 : ℝ) * HLm Γ 5 L425 + (-1 : ℝ) * HLm Γ 5 L427 := by
  have h := HLm_submod hΓ [F12] L428 [F68]
  rw [show [F12] ++ L428 ++ [F68] = L426 from rfl, show [F12] ++ L428 = L422 from rfl,
    show L428 ++ [F68] = L424 from rfl] at h
  rw [i173 hinj, i171 hinj, i172 hinj, i174 hinj] at h
  linarith

theorem row100 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L429 + (1 : ℝ) * HLm Γ 5 L431 + (-1 : ℝ) * HLm Γ 5 L433 + (-1 : ℝ) * HLm Γ 5 L427 := by
  have h := HLm_submod hΓ [F4] L428 [F26]
  rw [show [F4] ++ L428 ++ [F26] = L434 from rfl, show [F4] ++ L428 = L430 from rfl,
    show L428 ++ [F26] = L432 from rfl] at h
  rw [i177 hinj, i175 hinj, i176 hinj, i174 hinj] at h
  linarith

theorem row101 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L435 + (1 : ℝ) * HLm Γ 5 L323 + (-1 : ℝ) * HLm Γ 5 L437 + (-1 : ℝ) * HLm Γ 5 L427 := by
  have h := HLm_submod hΓ [F82] L428 [F27]
  rw [show [F82] ++ L428 ++ [F27] = L438 from rfl, show [F82] ++ L428 = L436 from rfl,
    show L428 ++ [F27] = L324 from rfl] at h
  rw [i179 hinj, i178 hinj, i126 hinj, i174 hinj] at h
  linarith

theorem row102 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L439 + (1 : ℝ) * HLm Γ 5 L441 + (-1 : ℝ) * HLm Γ 5 L443 + (-1 : ℝ) * HLm Γ 5 L427 := by
  have h := HLm_submod hΓ [F23] L428 [F88]
  rw [show [F23] ++ L428 ++ [F88] = L444 from rfl, show [F23] ++ L428 = L440 from rfl,
    show L428 ++ [F88] = L442 from rfl] at h
  rw [i182 hinj, i180 hinj, i181 hinj, i174 hinj] at h
  linarith

theorem row103 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L445 + (1 : ℝ) * HLm Γ 5 L447 + (-1 : ℝ) * HLm Γ 5 L449 + (-1 : ℝ) * HLm Γ 5 L427 := by
  have h := HLm_submod hΓ [F87] L428 [F14]
  rw [show [F87] ++ L428 ++ [F14] = L450 from rfl, show [F87] ++ L428 = L446 from rfl,
    show L428 ++ [F14] = L448 from rfl] at h
  rw [i185 hinj, i183 hinj, i184 hinj, i174 hinj] at h
  linarith

theorem row104 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L217 + (1 : ℝ) * HLm Γ 5 L452 + (-1 : ℝ) * HLm Γ 5 L454 + (-1 : ℝ) * HLm Γ 5 L456 := by
  have h := HLm_submod hΓ [F16] L456 [F25]
  rw [show [F16] ++ L456 ++ [F25] = L455 from rfl, show [F16] ++ L456 = L451 from rfl,
    show L456 ++ [F25] = L453 from rfl] at h
  rw [i188 hinj, i186 hinj, i187 hinj] at h
  linarith

theorem row105 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L120 + (1 : ℝ) * HLm Γ 5 L457 + (-1 : ℝ) * HLm Γ 5 L459 + (-1 : ℝ) * HLm Γ 5 L461 := by
  have h := HLm_submod hΓ [F7] L461 [F5]
  rw [show [F7] ++ L461 ++ [F5] = L460 from rfl, show [F7] ++ L461 = L120 from rfl,
    show L461 ++ [F5] = L458 from rfl] at h
  rw [i190 hinj, i189 hinj] at h
  linarith

theorem row106 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L120 + (1 : ℝ) * HLm Γ 5 L462 + (-1 : ℝ) * HLm Γ 5 L464 + (-1 : ℝ) * HLm Γ 5 L461 := by
  have h := HLm_submod hΓ [F7] L461 [F6]
  rw [show [F7] ++ L461 ++ [F6] = L465 from rfl, show [F7] ++ L461 = L120 from rfl,
    show L461 ++ [F6] = L463 from rfl] at h
  rw [i192 hinj, i191 hinj] at h
  linarith

theorem row107 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L96 + (1 : ℝ) * HLm Γ 5 L467 + (-1 : ℝ) * HLm Γ 5 L468 + (-1 : ℝ) * HLm Γ 5 L60 := by
  have h := HLm_submod hΓ [F0] L60 [F3]
  rw [show [F0] ++ L60 ++ [F3] = L469 from rfl, show [F0] ++ L60 = L466 from rfl,
    show L60 ++ [F3] = L467 from rfl] at h
  rw [i194 hinj, i193 hinj] at h
  linarith

theorem row108 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L470 + (1 : ℝ) * HLm Γ 5 L61 + (-1 : ℝ) * HLm Γ 5 L472 + (-1 : ℝ) * HLm Γ 5 L60 := by
  have h := HLm_submod hΓ [F16] L60 [F25]
  rw [show [F16] ++ L60 ++ [F25] = L473 from rfl, show [F16] ++ L60 = L471 from rfl,
    show L60 ++ [F25] = L61 from rfl] at h
  rw [i196 hinj, i195 hinj] at h
  linarith

theorem row109 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L474 + (1 : ℝ) * HLm Γ 5 L476 + (-1 : ℝ) * HLm Γ 5 L478 + (-1 : ℝ) * HLm Γ 5 L32 := by
  have h := HLm_submod hΓ [F2] L32 [F31]
  rw [show [F2] ++ L32 ++ [F31] = L479 from rfl, show [F2] ++ L32 = L475 from rfl,
    show L32 ++ [F31] = L477 from rfl] at h
  rw [i199 hinj, i197 hinj, i198 hinj] at h
  linarith

theorem row110 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L480 + (1 : ℝ) * HLm Γ 5 L482 + (-1 : ℝ) * HLm Γ 5 L483 + (-1 : ℝ) * HLm Γ 5 L32 := by
  have h := HLm_submod hΓ [F9] L32 [F3]
  rw [show [F9] ++ L32 ++ [F3] = L484 from rfl, show [F9] ++ L32 = L481 from rfl,
    show L32 ++ [F3] = L482 from rfl] at h
  rw [i201 hinj, i200 hinj] at h
  linarith

theorem row111 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L33 + (1 : ℝ) * HLm Γ 5 L485 + (-1 : ℝ) * HLm Γ 5 L487 + (-1 : ℝ) * HLm Γ 5 L32 := by
  have h := HLm_submod hΓ [F12] L32 [F16]
  rw [show [F12] ++ L32 ++ [F16] = L488 from rfl, show [F12] ++ L32 = L33 from rfl,
    show L32 ++ [F16] = L486 from rfl] at h
  rw [i203 hinj, i202 hinj] at h
  linarith

theorem row112 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L489 + (1 : ℝ) * HLm Γ 5 L491 + (-1 : ℝ) * HLm Γ 5 L493 + (-1 : ℝ) * HLm Γ 5 L81 := by
  have h := HLm_submod hΓ [F62] L81 [F16]
  rw [show [F62] ++ L81 ++ [F16] = L494 from rfl, show [F62] ++ L81 = L490 from rfl,
    show L81 ++ [F16] = L492 from rfl] at h
  rw [i206 hinj, i204 hinj, i205 hinj] at h
  linarith

theorem row113 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L495 + (1 : ℝ) * HLm Γ 5 L497 + (-1 : ℝ) * HLm Γ 5 L498 + (-1 : ℝ) * HLm Γ 5 L81 := by
  have h := HLm_submod hΓ [F3] L81 [F22]
  rw [show [F3] ++ L81 ++ [F22] = L499 from rfl, show [F3] ++ L81 = L496 from rfl,
    show L81 ++ [F22] = L497 from rfl] at h
  rw [i208 hinj, i207 hinj] at h
  linarith

theorem row114 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L500 + (1 : ℝ) * HLm Γ 5 L501 + (-1 : ℝ) * HLm Γ 5 L502 + (-1 : ℝ) * HLm Γ 5 L503 := by
  have h := HLm_submod hΓ [F0] L503 [F3]
  rw [show [F0] ++ L503 ++ [F3] = L502 from rfl, show [F0] ++ L503 = L500 from rfl,
    show L503 ++ [F3] = L501 from rfl] at h
  linarith

theorem row115 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L504 + (1 : ℝ) * HLm Γ 5 L501 + (-1 : ℝ) * HLm Γ 5 L506 + (-1 : ℝ) * HLm Γ 5 L503 := by
  have h := HLm_submod hΓ [F9] L503 [F3]
  rw [show [F9] ++ L503 ++ [F3] = L507 from rfl, show [F9] ++ L503 = L505 from rfl,
    show L503 ++ [F3] = L501 from rfl] at h
  rw [i210 hinj, i209 hinj] at h
  linarith

theorem row116 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L508 + (1 : ℝ) * HLm Γ 5 L509 + (-1 : ℝ) * HLm Γ 5 L511 + (-1 : ℝ) * HLm Γ 5 L503 := by
  have h := HLm_submod hΓ [F12] L503 [F16]
  rw [show [F12] ++ L503 ++ [F16] = L512 from rfl, show [F12] ++ L503 = L508 from rfl,
    show L503 ++ [F16] = L510 from rfl] at h
  rw [i212 hinj, i211 hinj] at h
  linarith

theorem row117 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L55 + (1 : ℝ) * HLm Γ 5 L514 + (-1 : ℝ) * HLm Γ 5 L516 + (-1 : ℝ) * HLm Γ 5 L503 := by
  have h := HLm_submod hΓ [F22] L503 [F5]
  rw [show [F22] ++ L503 ++ [F5] = L517 from rfl, show [F22] ++ L503 = L513 from rfl,
    show L503 ++ [F5] = L515 from rfl] at h
  rw [i215 hinj, i213 hinj, i214 hinj] at h
  linarith

theorem row118 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L55 + (1 : ℝ) * HLm Γ 5 L346 + (-1 : ℝ) * HLm Γ 5 L519 + (-1 : ℝ) * HLm Γ 5 L503 := by
  have h := HLm_submod hΓ [F22] L503 [F30]
  rw [show [F22] ++ L503 ++ [F30] = L520 from rfl, show [F22] ++ L503 = L513 from rfl,
    show L503 ++ [F30] = L518 from rfl] at h
  rw [i217 hinj, i213 hinj, i216 hinj] at h
  linarith

theorem row119 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L521 + (1 : ℝ) * HLm Γ 5 L523 + (-1 : ℝ) * HLm Γ 5 L524 + (-1 : ℝ) * HLm Γ 5 L84 := by
  have h := HLm_submod hΓ [F0] L84 [F2]
  rw [show [F0] ++ L84 ++ [F2] = L525 from rfl, show [F0] ++ L84 = L522 from rfl,
    show L84 ++ [F2] = L523 from rfl] at h
  rw [i219 hinj, i218 hinj] at h
  linarith

theorem row120 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L526 + (1 : ℝ) * HLm Γ 5 L528 + (-1 : ℝ) * HLm Γ 5 L530 + (-1 : ℝ) * HLm Γ 5 L84 := by
  have h := HLm_submod hΓ [F9] L84 [F72]
  rw [show [F9] ++ L84 ++ [F72] = L531 from rfl, show [F9] ++ L84 = L527 from rfl,
    show L84 ++ [F72] = L529 from rfl] at h
  rw [i222 hinj, i220 hinj, i221 hinj] at h
  linarith

theorem row121 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L532 + (1 : ℝ) * HLm Γ 5 L534 + (-1 : ℝ) * HLm Γ 5 L536 + (-1 : ℝ) * HLm Γ 5 L85 := by
  have h := HLm_submod hΓ [F7] L85 [F96]
  rw [show [F7] ++ L85 ++ [F96] = L537 from rfl, show [F7] ++ L85 = L533 from rfl,
    show L85 ++ [F96] = L535 from rfl] at h
  rw [i225 hinj, i223 hinj, i224 hinj] at h
  linarith

theorem row122 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L538 + (1 : ℝ) * HLm Γ 5 L540 + (-1 : ℝ) * HLm Γ 5 L542 + (-1 : ℝ) * HLm Γ 5 L85 := by
  have h := HLm_submod hΓ [F62] L85 [F16]
  rw [show [F62] ++ L85 ++ [F16] = L543 from rfl, show [F62] ++ L85 = L539 from rfl,
    show L85 ++ [F16] = L541 from rfl] at h
  rw [i228 hinj, i226 hinj, i227 hinj] at h
  linarith

theorem row123 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L544 + (1 : ℝ) * HLm Γ 5 L545 + (-1 : ℝ) * HLm Γ 5 L547 + (-1 : ℝ) * HLm Γ 5 L549 := by
  have h := HLm_submod hΓ [F0] L549 [F34]
  rw [show [F0] ++ L549 ++ [F34] = L548 from rfl, show [F0] ++ L549 = L544 from rfl,
    show L549 ++ [F34] = L546 from rfl] at h
  rw [i230 hinj, i229 hinj] at h
  linarith

theorem row124 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L550 + (1 : ℝ) * HLm Γ 5 L552 + (-1 : ℝ) * HLm Γ 5 L553 + (-1 : ℝ) * HLm Γ 5 L252 := by
  have h := HLm_submod hΓ [F16] L252 [F67]
  rw [show [F16] ++ L252 ++ [F67] = L554 from rfl, show [F16] ++ L252 = L551 from rfl,
    show L252 ++ [F67] = L552 from rfl] at h
  rw [i232 hinj, i231 hinj] at h
  linarith

theorem row125 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L555 + (1 : ℝ) * HLm Γ 5 L557 + (-1 : ℝ) * HLm Γ 5 L558 + (-1 : ℝ) * HLm Γ 5 L94 := by
  have h := HLm_submod hΓ [F1] L94 [F16]
  rw [show [F1] ++ L94 ++ [F16] = L559 from rfl, show [F1] ++ L94 = L556 from rfl,
    show L94 ++ [F16] = L557 from rfl] at h
  rw [i234 hinj, i233 hinj] at h
  linarith

theorem row126 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L560 + (1 : ℝ) * HLm Γ 5 L562 + (-1 : ℝ) * HLm Γ 5 L563 + (-1 : ℝ) * HLm Γ 5 L94 := by
  have h := HLm_submod hΓ [F107] L94 [F48]
  rw [show [F107] ++ L94 ++ [F48] = L564 from rfl, show [F107] ++ L94 = L561 from rfl,
    show L94 ++ [F48] = L562 from rfl] at h
  rw [i236 hinj, i235 hinj] at h
  linarith

theorem row127 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L565 + (1 : ℝ) * HLm Γ 5 L567 + (-1 : ℝ) * HLm Γ 5 L568 + (-1 : ℝ) * HLm Γ 5 L99 := by
  have h := HLm_submod hΓ [F1] L99 [F48]
  rw [show [F1] ++ L99 ++ [F48] = L569 from rfl, show [F1] ++ L99 = L566 from rfl,
    show L99 ++ [F48] = L567 from rfl] at h
  rw [i238 hinj, i237 hinj] at h
  linarith

theorem row128 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L570 + (1 : ℝ) * HLm Γ 5 L572 + (-1 : ℝ) * HLm Γ 5 L573 + (-1 : ℝ) * HLm Γ 5 L575 := by
  have h := HLm_submod hΓ [F2] L575 [F67]
  rw [show [F2] ++ L575 ++ [F67] = L574 from rfl, show [F2] ++ L575 = L571 from rfl,
    show L575 ++ [F67] = L572 from rfl] at h
  rw [i240 hinj, i239 hinj] at h
  linarith

theorem row129 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L576 + (1 : ℝ) * HLm Γ 5 L235 + (-1 : ℝ) * HLm Γ 5 L578 + (-1 : ℝ) * HLm Γ 5 L233 := by
  have h := HLm_submod hΓ [F7] L233 [F3]
  rw [show [F7] ++ L233 ++ [F3] = L579 from rfl, show [F7] ++ L233 = L577 from rfl,
    show L233 ++ [F3] = L235 from rfl] at h
  rw [i242 hinj, i241 hinj] at h
  linarith

theorem row130 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L580 + (1 : ℝ) * HLm Γ 5 L582 + (-1 : ℝ) * HLm Γ 5 L583 + (-1 : ℝ) * HLm Γ 5 L288 := by
  have h := HLm_submod hΓ [F44] L288 [F48]
  rw [show [F44] ++ L288 ++ [F48] = L584 from rfl, show [F44] ++ L288 = L581 from rfl,
    show L288 ++ [F48] = L582 from rfl] at h
  rw [i244 hinj, i243 hinj] at h
  linarith

theorem row131 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L157 + (1 : ℝ) * HLm Γ 5 L586 + (-1 : ℝ) * HLm Γ 5 L588 + (-1 : ℝ) * HLm Γ 5 L327 := by
  have h := HLm_submod hΓ [F7] L328 [F82]
  rw [show [F7] ++ L328 ++ [F82] = L589 from rfl, show [F7] ++ L328 = L585 from rfl,
    show L328 ++ [F82] = L587 from rfl] at h
  rw [i247 hinj, i245 hinj, i246 hinj, i128 hinj] at h
  linarith

theorem row132 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L235 + (1 : ℝ) * HLm Γ 5 L547 + (-1 : ℝ) * HLm Γ 5 L592 + (-1 : ℝ) * HLm Γ 5 L393 := by
  have h := HLm_submod hΓ [F3] L393 [F105]
  rw [show [F3] ++ L393 ++ [F105] = L593 from rfl, show [F3] ++ L393 = L590 from rfl,
    show L393 ++ [F105] = L591 from rfl] at h
  rw [i250 hinj, i248 hinj, i249 hinj] at h
  linarith

theorem row133 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L468 + (1 : ℝ) * HLm Γ 5 L595 + (-1 : ℝ) * HLm Γ 5 L597 + (-1 : ℝ) * HLm Γ 5 L96 := by
  have h := HLm_submod hΓ [F3] L96 [F16]
  rw [show [F3] ++ L96 ++ [F16] = L598 from rfl, show [F3] ++ L96 = L594 from rfl,
    show L96 ++ [F16] = L596 from rfl] at h
  rw [i253 hinj, i251 hinj, i252 hinj] at h
  linarith

theorem row134 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L97 + (1 : ℝ) * HLm Γ 5 L595 + (-1 : ℝ) * HLm Γ 5 L599 + (-1 : ℝ) * HLm Γ 5 L96 := by
  have h := HLm_submod hΓ [F44] L96 [F16]
  rw [show [F44] ++ L96 ++ [F16] = L600 from rfl, show [F44] ++ L96 = L98 from rfl,
    show L96 ++ [F16] = L596 from rfl] at h
  rw [i254 hinj, i25 hinj, i252 hinj] at h
  linarith

theorem row135 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L295 + (1 : ℝ) * HLm Γ 5 L602 + (-1 : ℝ) * HLm Γ 5 L604 + (-1 : ℝ) * HLm Γ 5 L500 := by
  have h := HLm_submod hΓ [F22] L500 [F105]
  rw [show [F22] ++ L500 ++ [F105] = L605 from rfl, show [F22] ++ L500 = L601 from rfl,
    show L500 ++ [F105] = L603 from rfl] at h
  rw [i257 hinj, i255 hinj, i256 hinj] at h
  linarith

theorem row136 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L29 + (1 : ℝ) * HLm Γ 5 L607 + (-1 : ℝ) * HLm Γ 5 L609 + (-1 : ℝ) * HLm Γ 5 L611 := by
  have h := HLm_submod hΓ [F7] L611 [F108]
  rw [show [F7] ++ L611 ++ [F108] = L610 from rfl, show [F7] ++ L611 = L606 from rfl,
    show L611 ++ [F108] = L608 from rfl] at h
  rw [i260 hinj, i258 hinj, i259 hinj] at h
  linarith

theorem row137 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L82 + (1 : ℝ) * HLm Γ 5 L301 + (-1 : ℝ) * HLm Γ 5 L614 + (-1 : ℝ) * HLm Γ 5 L616 := by
  have h := HLm_submod hΓ [F2] L617 [F27]
  rw [show [F2] ++ L617 ++ [F27] = L615 from rfl, show [F2] ++ L617 = L612 from rfl,
    show L617 ++ [F27] = L613 from rfl] at h
  rw [i263 hinj, i261 hinj, i262 hinj, i264 hinj] at h
  linarith

theorem row138 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L17 + (1 : ℝ) * HLm Γ 5 L619 + (-1 : ℝ) * HLm Γ 5 L621 + (-1 : ℝ) * HLm Γ 5 L623 := by
  have h := HLm_submod hΓ [F1] L623 [F21]
  rw [show [F1] ++ L623 ++ [F21] = L622 from rfl, show [F1] ++ L623 = L618 from rfl,
    show L623 ++ [F21] = L620 from rfl] at h
  rw [i267 hinj, i265 hinj, i266 hinj] at h
  linarith

theorem row139 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L624 + (1 : ℝ) * HLm Γ 5 L626 + (-1 : ℝ) * HLm Γ 5 L627 + (-1 : ℝ) * HLm Γ 5 L623 := by
  have h := HLm_submod hΓ [F51] L623 [F48]
  rw [show [F51] ++ L623 ++ [F48] = L628 from rfl, show [F51] ++ L623 = L625 from rfl,
    show L623 ++ [F48] = L626 from rfl] at h
  rw [i269 hinj, i268 hinj] at h
  linarith

theorem row140 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L629 + (1 : ℝ) * HLm Γ 5 L631 + (-1 : ℝ) * HLm Γ 5 L633 + (-1 : ℝ) * HLm Γ 5 L303 := by
  have h := HLm_submod hΓ [F67] L635 [F59]
  rw [show [F67] ++ L635 ++ [F59] = L634 from rfl, show [F67] ++ L635 = L630 from rfl,
    show L635 ++ [F59] = L632 from rfl] at h
  rw [i272 hinj, i270 hinj, i271 hinj, i273 hinj] at h
  linarith

theorem row141 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L89 + (1 : ℝ) * HLm Γ 5 L636 + (-1 : ℝ) * HLm Γ 5 L638 + (-1 : ℝ) * HLm Γ 5 L640 := by
  have h := HLm_submod hΓ [F0] L640 [F1]
  rw [show [F0] ++ L640 ++ [F1] = L639 from rfl, show [F0] ++ L640 = L89 from rfl,
    show L640 ++ [F1] = L637 from rfl] at h
  rw [i275 hinj, i274 hinj] at h
  linarith

theorem row142 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L576 + (1 : ℝ) * HLm Γ 5 L642 + (-1 : ℝ) * HLm Γ 5 L644 + (-1 : ℝ) * HLm Γ 5 L646 := by
  have h := HLm_submod hΓ [F0] L647 [F19]
  rw [show [F0] ++ L647 ++ [F19] = L645 from rfl, show [F0] ++ L647 = L641 from rfl,
    show L647 ++ [F19] = L643 from rfl] at h
  rw [i278 hinj, i276 hinj, i277 hinj, i279 hinj] at h
  linarith

theorem row143 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L648 + (1 : ℝ) * HLm Γ 5 L650 + (-1 : ℝ) * HLm Γ 5 L652 + (-1 : ℝ) * HLm Γ 5 L646 := by
  have h := HLm_submod hΓ [F2] L647 [F29]
  rw [show [F2] ++ L647 ++ [F29] = L653 from rfl, show [F2] ++ L647 = L649 from rfl,
    show L647 ++ [F29] = L651 from rfl] at h
  rw [i282 hinj, i280 hinj, i281 hinj, i279 hinj] at h
  linarith

theorem row144 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L654 + (1 : ℝ) * HLm Γ 5 L656 + (-1 : ℝ) * HLm Γ 5 L658 + (-1 : ℝ) * HLm Γ 5 L660 := by
  have h := HLm_submod hΓ [F3] L661 [F52]
  rw [show [F3] ++ L661 ++ [F52] = L659 from rfl, show [F3] ++ L661 = L655 from rfl,
    show L661 ++ [F52] = L657 from rfl] at h
  rw [i285 hinj, i283 hinj, i284 hinj, i286 hinj] at h
  linarith

theorem row145 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L662 + (1 : ℝ) * HLm Γ 5 L664 + (-1 : ℝ) * HLm Γ 5 L666 + (-1 : ℝ) * HLm Γ 5 L660 := by
  have h := HLm_submod hΓ [F34] L661 [F38]
  rw [show [F34] ++ L661 ++ [F38] = L667 from rfl, show [F34] ++ L661 = L663 from rfl,
    show L661 ++ [F38] = L665 from rfl] at h
  rw [i289 hinj, i287 hinj, i288 hinj, i286 hinj] at h
  linarith

theorem row146 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L668 + (1 : ℝ) * HLm Γ 5 L459 + (-1 : ℝ) * HLm Γ 5 L669 + (-1 : ℝ) * HLm Γ 5 L120 := by
  have h := HLm_submod hΓ [F0] L120 [F5]
  rw [show [F0] ++ L120 ++ [F5] = L670 from rfl, show [F0] ++ L120 = L668 from rfl,
    show L120 ++ [F5] = L460 from rfl] at h
  rw [i290 hinj, i190 hinj] at h
  linarith

theorem row147 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L671 + (1 : ℝ) * HLm Γ 5 L673 + (-1 : ℝ) * HLm Γ 5 L675 + (-1 : ℝ) * HLm Γ 5 L677 := by
  have h := HLm_submod hΓ [F2] L678 [F16]
  rw [show [F2] ++ L678 ++ [F16] = L676 from rfl, show [F2] ++ L678 = L672 from rfl,
    show L678 ++ [F16] = L674 from rfl] at h
  rw [i293 hinj, i291 hinj, i292 hinj, i294 hinj] at h
  linarith

theorem row148 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L679 + (1 : ℝ) * HLm Γ 5 L681 + (-1 : ℝ) * HLm Γ 5 L683 + (-1 : ℝ) * HLm Γ 5 L532 := by
  have h := HLm_submod hΓ [F0] L685 [F1]
  rw [show [F0] ++ L685 ++ [F1] = L684 from rfl, show [F0] ++ L685 = L680 from rfl,
    show L685 ++ [F1] = L682 from rfl] at h
  rw [i297 hinj, i295 hinj, i296 hinj, i298 hinj] at h
  linarith

theorem row149 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L686 + (1 : ℝ) * HLm Γ 5 L124 + (-1 : ℝ) * HLm Γ 5 L689 + (-1 : ℝ) * HLm Γ 5 L122 := by
  have h := HLm_submod hΓ [F0] L123 [F48]
  rw [show [F0] ++ L123 ++ [F48] = L690 from rfl, show [F0] ++ L123 = L687 from rfl,
    show L123 ++ [F48] = L688 from rfl] at h
  rw [i301 hinj, i299 hinj, i300 hinj, i35 hinj] at h
  linarith

end EntropyBounds.TwoSet.Certs.R7A5
