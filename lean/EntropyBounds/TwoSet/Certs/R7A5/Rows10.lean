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

theorem row1500 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3236 + (1 : ℝ) * HLm Γ 5 L7171 + (-1 : ℝ) * HLm Γ 5 L7172 + (-1 : ℝ) * HLm Γ 5 L233 := by
  have h := HLm_submod hΓ [F67] L233 [F214]
  rw [show [F67] ++ L233 ++ [F214] = L7173 from rfl, show [F67] ++ L233 = L7170 from rfl,
    show L233 ++ [F214] = L7171 from rfl] at h
  rw [i4255 hinj, i4254 hinj] at h
  linarith

theorem row1501 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L89 + (1 : ℝ) * HLm Γ 5 L7174 + (-1 : ℝ) * HLm Γ 5 L3248 + (-1 : ℝ) * HLm Γ 5 L12 := by
  have h := HLm_submod hΓ [F7] L12 [F82]
  rw [show [F7] ++ L12 ++ [F82] = L7176 from rfl, show [F7] ++ L12 = L90 from rfl,
    show L12 ++ [F82] = L7175 from rfl] at h
  rw [i4257 hinj, i22 hinj, i4256 hinj] at h
  linarith

theorem row1502 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7177 + (1 : ℝ) * HLm Γ 5 L330 + (-1 : ℝ) * HLm Γ 5 L3883 + (-1 : ℝ) * HLm Γ 5 L6931 := by
  have h := HLm_submod hΓ [F210] L6931 [F86]
  rw [show [F210] ++ L6931 ++ [F86] = L7179 from rfl, show [F210] ++ L6931 = L7178 from rfl,
    show L6931 ++ [F86] = L3881 from rfl] at h
  rw [i4259 hinj, i4258 hinj, i2167 hinj] at h
  linarith

theorem row1503 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3009 + (1 : ℝ) * HLm Γ 5 L4065 + (-1 : ℝ) * HLm Γ 5 L3012 + (-1 : ℝ) * HLm Γ 5 L6807 := by
  have h := HLm_submod hΓ [F7] L6807 [F6]
  rw [show [F7] ++ L6807 ++ [F6] = L4293 from rfl, show [F7] ++ L6807 = L7180 from rfl,
    show L6807 ++ [F6] = L4065 from rfl] at h
  rw [i2403 hinj, i4260 hinj] at h
  linarith

theorem row1504 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L580 + (1 : ℝ) * HLm Γ 5 L7181 + (-1 : ℝ) * HLm Γ 5 L7182 + (-1 : ℝ) * HLm Γ 5 L288 := by
  have h := HLm_submod hΓ [F44] L288 [F217]
  rw [show [F44] ++ L288 ++ [F217] = L7183 from rfl, show [F44] ++ L288 = L581 from rfl,
    show L288 ++ [F217] = L7181 from rfl] at h
  rw [i4261 hinj, i243 hinj] at h
  linarith

theorem row1505 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7184 + (1 : ℝ) * HLm Γ 5 L7186 + (-1 : ℝ) * HLm Γ 5 L7188 + (-1 : ℝ) * HLm Γ 5 L288 := by
  have h := HLm_submod hΓ [F210] L288 [F6]
  rw [show [F210] ++ L288 ++ [F6] = L7189 from rfl, show [F210] ++ L288 = L7185 from rfl,
    show L288 ++ [F6] = L7187 from rfl] at h
  rw [i4264 hinj, i4262 hinj, i4263 hinj] at h
  linarith

theorem row1506 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7190 + (1 : ℝ) * HLm Γ 5 L7192 + (-1 : ℝ) * HLm Γ 5 L7194 + (-1 : ℝ) * HLm Γ 5 L327 := by
  have h := HLm_submod hΓ [F210] L328 [F43]
  rw [show [F210] ++ L328 ++ [F43] = L7195 from rfl, show [F210] ++ L328 = L7191 from rfl,
    show L328 ++ [F43] = L7193 from rfl] at h
  rw [i4267 hinj, i4265 hinj, i4266 hinj, i128 hinj] at h
  linarith

theorem row1507 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3087 + (1 : ℝ) * HLm Γ 5 L7197 + (-1 : ℝ) * HLm Γ 5 L3886 + (-1 : ℝ) * HLm Γ 5 L3086 := by
  have h := HLm_submod hΓ [F67] L3086 [F210]
  rw [show [F67] ++ L3086 ++ [F210] = L7198 from rfl, show [F67] ++ L3086 = L7196 from rfl,
    show L3086 ++ [F210] = L7197 from rfl] at h
  rw [i4269 hinj, i4268 hinj] at h
  linarith

theorem row1508 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3247 + (1 : ℝ) * HLm Γ 5 L7200 + (-1 : ℝ) * HLm Γ 5 L7202 + (-1 : ℝ) * HLm Γ 5 L3086 := by
  have h := HLm_submod hΓ [F82] L3086 [F228]
  rw [show [F82] ++ L3086 ++ [F228] = L7203 from rfl, show [F82] ++ L3086 = L7199 from rfl,
    show L3086 ++ [F228] = L7201 from rfl] at h
  rw [i4272 hinj, i4270 hinj, i4271 hinj] at h
  linarith

theorem row1509 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7204 + (1 : ℝ) * HLm Γ 5 L2471 + (-1 : ℝ) * HLm Γ 5 L7206 + (-1 : ℝ) * HLm Γ 5 L7048 := by
  have h := HLm_submod hΓ [F108] L7048 [F67]
  rw [show [F108] ++ L7048 ++ [F67] = L7207 from rfl, show [F108] ++ L7048 = L7205 from rfl,
    show L7048 ++ [F67] = L2471 from rfl] at h
  rw [i4274 hinj, i4273 hinj] at h
  linarith

theorem row1510 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7208 + (1 : ℝ) * HLm Γ 5 L7210 + (-1 : ℝ) * HLm Γ 5 L7212 + (-1 : ℝ) * HLm Γ 5 L7048 := by
  have h := HLm_submod hΓ [F228] L7048 [F45]
  rw [show [F228] ++ L7048 ++ [F45] = L7213 from rfl, show [F228] ++ L7048 = L7209 from rfl,
    show L7048 ++ [F45] = L7211 from rfl] at h
  rw [i4277 hinj, i4275 hinj, i4276 hinj] at h
  linarith

theorem row1511 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L106 + (1 : ℝ) * HLm Γ 5 L4045 + (-1 : ℝ) * HLm Γ 5 L4048 + (-1 : ℝ) * HLm Γ 5 L14 := by
  have h := HLm_submod hΓ [F16] L14 [F210]
  rw [show [F16] ++ L14 ++ [F210] = L7215 from rfl, show [F16] ++ L14 = L7214 from rfl,
    show L14 ++ [F210] = L4045 from rfl] at h
  rw [i4279 hinj, i4278 hinj] at h
  linarith

theorem row1512 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L565 + (1 : ℝ) * HLm Γ 5 L2950 + (-1 : ℝ) * HLm Γ 5 L7216 + (-1 : ℝ) * HLm Γ 5 L2946 := by
  have h := HLm_submod hΓ [F0] L2947 [F218]
  rw [show [F0] ++ L2947 ++ [F218] = L7217 from rfl, show [F0] ++ L2947 = L1248 from rfl,
    show L2947 ++ [F218] = L2951 from rfl] at h
  rw [i4280 hinj, i606 hinj, i1681 hinj, i1679 hinj] at h
  linarith

theorem row1513 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7218 + (1 : ℝ) * HLm Γ 5 L7219 + (-1 : ℝ) * HLm Γ 5 L7221 + (-1 : ℝ) * HLm Γ 5 L7223 := by
  have h := HLm_submod hΓ [F27] L7223 [F218]
  rw [show [F27] ++ L7223 ++ [F218] = L7222 from rfl, show [F27] ++ L7223 = L7218 from rfl,
    show L7223 ++ [F218] = L7220 from rfl] at h
  rw [i4282 hinj, i4281 hinj] at h
  linarith

theorem row1514 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3939 + (1 : ℝ) * HLm Γ 5 L6979 + (-1 : ℝ) * HLm Γ 5 L3943 + (-1 : ℝ) * HLm Γ 5 L7227 := by
  have h := HLm_submod hΓ [F214] L7227 [F27]
  rw [show [F214] ++ L7227 ++ [F27] = L7226 from rfl, show [F214] ++ L7227 = L7224 from rfl,
    show L7227 ++ [F27] = L7225 from rfl] at h
  rw [i4285 hinj, i4283 hinj, i4284 hinj] at h
  linarith

theorem row1515 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7228 + (1 : ℝ) * HLm Γ 5 L7230 + (-1 : ℝ) * HLm Γ 5 L7232 + (-1 : ℝ) * HLm Γ 5 L7234 := by
  have h := HLm_submod hΓ [F2] L7235 [F27]
  rw [show [F2] ++ L7235 ++ [F27] = L7233 from rfl, show [F2] ++ L7235 = L7229 from rfl,
    show L7235 ++ [F27] = L7231 from rfl] at h
  rw [i4288 hinj, i4286 hinj, i4287 hinj, i4289 hinj] at h
  linarith

theorem row1516 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7230 + (1 : ℝ) * HLm Γ 5 L7237 + (-1 : ℝ) * HLm Γ 5 L7239 + (-1 : ℝ) * HLm Γ 5 L297 := by
  have h := HLm_submod hΓ [F68] L298 [F214]
  rw [show [F68] ++ L298 ++ [F214] = L7240 from rfl, show [F68] ++ L298 = L7236 from rfl,
    show L298 ++ [F214] = L7238 from rfl] at h
  rw [i4292 hinj, i4290 hinj, i4291 hinj, i114 hinj] at h
  linarith

theorem row1517 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7241 + (1 : ℝ) * HLm Γ 5 L6981 + (-1 : ℝ) * HLm Γ 5 L7243 + (-1 : ℝ) * HLm Γ 5 L297 := by
  have h := HLm_submod hΓ [F210] L298 [F45]
  rw [show [F210] ++ L298 ++ [F45] = L7244 from rfl, show [F210] ++ L298 = L7242 from rfl,
    show L298 ++ [F45] = L6982 from rfl] at h
  rw [i4294 hinj, i4293 hinj, i4146 hinj, i114 hinj] at h
  linarith

theorem row1518 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3298 + (1 : ℝ) * HLm Γ 5 L7245 + (-1 : ℝ) * HLm Γ 5 L7247 + (-1 : ℝ) * HLm Γ 5 L3303 := by
  have h := HLm_submod hΓ [F7] L3303 [F214]
  rw [show [F7] ++ L3303 ++ [F214] = L7248 from rfl, show [F7] ++ L3303 = L3298 from rfl,
    show L3303 ++ [F214] = L7246 from rfl] at h
  rw [i4296 hinj, i4295 hinj] at h
  linarith

theorem row1519 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L707 + (1 : ℝ) * HLm Γ 5 L7249 + (-1 : ℝ) * HLm Γ 5 L7251 + (-1 : ℝ) * HLm Γ 5 L2001 := by
  have h := HLm_submod hΓ [F2] L2002 [F217]
  rw [show [F2] ++ L2002 ++ [F217] = L7252 from rfl, show [F2] ++ L2002 = L2229 from rfl,
    show L2002 ++ [F217] = L7250 from rfl] at h
  rw [i4298 hinj, i1225 hinj, i4297 hinj, i1097 hinj] at h
  linarith

theorem row1520 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L181 + (1 : ℝ) * HLm Γ 5 L7254 + (-1 : ℝ) * HLm Γ 5 L2438 + (-1 : ℝ) * HLm Γ 5 L178 := by
  have h := HLm_submod hΓ [F16] L179 [F67]
  rw [show [F16] ++ L179 ++ [F67] = L7256 from rfl, show [F16] ++ L179 = L7253 from rfl,
    show L179 ++ [F67] = L7255 from rfl] at h
  rw [i4301 hinj, i4299 hinj, i4300 hinj, i61 hinj] at h
  linarith

theorem row1521 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7257 + (1 : ℝ) * HLm Γ 5 L7259 + (-1 : ℝ) * HLm Γ 5 L1418 + (-1 : ℝ) * HLm Γ 5 L623 := by
  have h := HLm_submod hΓ [F16] L623 [F67]
  rw [show [F16] ++ L623 ++ [F67] = L7260 from rfl, show [F16] ++ L623 = L7258 from rfl,
    show L623 ++ [F67] = L7259 from rfl] at h
  rw [i4303 hinj, i4302 hinj] at h
  linarith

theorem row1522 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4416 + (1 : ℝ) * HLm Γ 5 L2579 + (-1 : ℝ) * HLm Γ 5 L3401 + (-1 : ℝ) * HLm Γ 5 L623 := by
  have h := HLm_submod hΓ [F211] L623 [F6]
  rw [show [F211] ++ L623 ++ [F6] = L7261 from rfl, show [F211] ++ L623 = L4416 from rfl,
    show L623 ++ [F6] = L2580 from rfl] at h
  rw [i4304 hinj, i1439 hinj] at h
  linarith

theorem row1523 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1363 + (1 : ℝ) * HLm Γ 5 L7263 + (-1 : ℝ) * HLm Γ 5 L1719 + (-1 : ℝ) * HLm Γ 5 L17 := by
  have h := HLm_submod hΓ [F16] L18 [F67]
  rw [show [F16] ++ L18 ++ [F67] = L7265 from rfl, show [F16] ++ L18 = L7262 from rfl,
    show L18 ++ [F67] = L7264 from rfl] at h
  rw [i4307 hinj, i4305 hinj, i4306 hinj, i2 hinj] at h
  linarith

theorem row1524 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L576 + (1 : ℝ) * HLm Γ 5 L118 + (-1 : ℝ) * HLm Γ 5 L2241 + (-1 : ℝ) * HLm Γ 5 L110 := by
  have h := HLm_submod hΓ [F0] L110 [F23]
  rw [show [F0] ++ L110 ++ [F23] = L7267 from rfl, show [F0] ++ L110 = L576 from rfl,
    show L110 ++ [F23] = L7266 from rfl] at h
  rw [i4309 hinj, i4308 hinj] at h
  linarith

theorem row1525 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7268 + (1 : ℝ) * HLm Γ 5 L1431 + (-1 : ℝ) * HLm Γ 5 L7270 + (-1 : ℝ) * HLm Γ 5 L303 := by
  have h := HLm_submod hΓ [F214] L635 [F45]
  rw [show [F214] ++ L635 ++ [F45] = L7271 from rfl, show [F214] ++ L635 = L7269 from rfl,
    show L635 ++ [F45] = L3332 from rfl] at h
  rw [i4311 hinj, i4310 hinj, i1876 hinj, i273 hinj] at h
  linarith

theorem row1526 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4437 + (1 : ℝ) * HLm Γ 5 L7273 + (-1 : ℝ) * HLm Γ 5 L7274 + (-1 : ℝ) * HLm Γ 5 L3339 := by
  have h := HLm_submod hΓ [F82] L3339 [F214]
  rw [show [F82] ++ L3339 ++ [F214] = L7275 from rfl, show [F82] ++ L3339 = L7272 from rfl,
    show L3339 ++ [F214] = L7273 from rfl] at h
  rw [i4313 hinj, i4312 hinj] at h
  linarith

theorem row1527 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3563 + (1 : ℝ) * HLm Γ 5 L2869 + (-1 : ℝ) * HLm Γ 5 L7278 + (-1 : ℝ) * HLm Γ 5 L2866 := by
  have h := HLm_submod hΓ [F0] L7280 [F36]
  rw [show [F0] ++ L7280 ++ [F36] = L7279 from rfl, show [F0] ++ L7280 = L7276 from rfl,
    show L7280 ++ [F36] = L7277 from rfl] at h
  rw [i4316 hinj, i4314 hinj, i4315 hinj, i4317 hinj] at h
  linarith

theorem row1528 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7281 + (1 : ℝ) * HLm Γ 5 L7283 + (-1 : ℝ) * HLm Γ 5 L7285 + (-1 : ℝ) * HLm Γ 5 L117 := by
  have h := HLm_submod hΓ [F236] L117 [F85]
  rw [show [F236] ++ L117 ++ [F85] = L7286 from rfl, show [F236] ++ L117 = L7282 from rfl,
    show L117 ++ [F85] = L7284 from rfl] at h
  rw [i4320 hinj, i4318 hinj, i4319 hinj] at h
  linarith

theorem row1529 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7287 + (1 : ℝ) * HLm Γ 5 L4513 + (-1 : ℝ) * HLm Γ 5 L7289 + (-1 : ℝ) * HLm Γ 5 L7291 := by
  have h := HLm_submod hΓ [F111] L7292 [F45]
  rw [show [F111] ++ L7292 ++ [F45] = L7290 from rfl, show [F111] ++ L7292 = L7288 from rfl,
    show L7292 ++ [F45] = L4514 from rfl] at h
  rw [i4322 hinj, i4321 hinj, i2528 hinj, i4323 hinj] at h
  linarith

theorem row1530 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6999 + (1 : ℝ) * HLm Γ 5 L7294 + (-1 : ℝ) * HLm Γ 5 L7296 + (-1 : ℝ) * HLm Γ 5 L6997 := by
  have h := HLm_submod hΓ [F67] L6998 [F210]
  rw [show [F67] ++ L6998 ++ [F210] = L7297 from rfl, show [F67] ++ L6998 = L7293 from rfl,
    show L6998 ++ [F210] = L7295 from rfl] at h
  rw [i4326 hinj, i4324 hinj, i4325 hinj, i4156 hinj] at h
  linarith

theorem row1531 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7298 + (1 : ℝ) * HLm Γ 5 L7300 + (-1 : ℝ) * HLm Γ 5 L7302 + (-1 : ℝ) * HLm Γ 5 L3377 := by
  have h := HLm_submod hΓ [F1] L3378 [F218]
  rw [show [F1] ++ L3378 ++ [F218] = L7303 from rfl, show [F1] ++ L3378 = L7299 from rfl,
    show L3378 ++ [F218] = L7301 from rfl] at h
  rw [i4329 hinj, i4327 hinj, i4328 hinj, i1897 hinj] at h
  linarith

theorem row1532 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L74 + (1 : ℝ) * HLm Γ 5 L7304 + (-1 : ℝ) * HLm Γ 5 L7306 + (-1 : ℝ) * HLm Γ 5 L6810 := by
  have h := HLm_submod hΓ [F0] L6811 [F43]
  rw [show [F0] ++ L6811 ++ [F43] = L7307 from rfl, show [F0] ++ L6811 = L6812 from rfl,
    show L6811 ++ [F43] = L7305 from rfl] at h
  rw [i4331 hinj, i4059 hinj, i4330 hinj, i4058 hinj] at h
  linarith

theorem row1533 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7308 + (1 : ℝ) * HLm Γ 5 L7310 + (-1 : ℝ) * HLm Γ 5 L7312 + (-1 : ℝ) * HLm Γ 5 L6810 := by
  have h := HLm_submod hΓ [F67] L6811 [F214]
  rw [show [F67] ++ L6811 ++ [F214] = L7313 from rfl, show [F67] ++ L6811 = L7309 from rfl,
    show L6811 ++ [F214] = L7311 from rfl] at h
  rw [i4334 hinj, i4332 hinj, i4333 hinj, i4058 hinj] at h
  linarith

theorem row1534 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7314 + (1 : ℝ) * HLm Γ 5 L7316 + (-1 : ℝ) * HLm Γ 5 L7318 + (-1 : ℝ) * HLm Γ 5 L646 := by
  have h := HLm_submod hΓ [F111] L647 [F67]
  rw [show [F111] ++ L647 ++ [F67] = L7319 from rfl, show [F111] ++ L647 = L7315 from rfl,
    show L647 ++ [F67] = L7317 from rfl] at h
  rw [i4337 hinj, i4335 hinj, i4336 hinj, i279 hinj] at h
  linarith

theorem row1535 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L157 + (1 : ℝ) * HLm Γ 5 L654 + (-1 : ℝ) * HLm Γ 5 L7321 + (-1 : ℝ) * HLm Γ 5 L660 := by
  have h := HLm_submod hΓ [F0] L661 [F3]
  rw [show [F0] ++ L661 ++ [F3] = L7322 from rfl, show [F0] ++ L661 = L2243 from rfl,
    show L661 ++ [F3] = L7320 from rfl] at h
  rw [i4339 hinj, i1233 hinj, i4338 hinj, i286 hinj] at h
  linarith

theorem row1536 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L157 + (1 : ℝ) * HLm Γ 5 L662 + (-1 : ℝ) * HLm Γ 5 L788 + (-1 : ℝ) * HLm Γ 5 L660 := by
  have h := HLm_submod hΓ [F0] L661 [F34]
  rw [show [F0] ++ L661 ++ [F34] = L7324 from rfl, show [F0] ++ L661 = L2243 from rfl,
    show L661 ++ [F34] = L7323 from rfl] at h
  rw [i4341 hinj, i1233 hinj, i4340 hinj, i286 hinj] at h
  linarith

theorem row1537 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7325 + (1 : ℝ) * HLm Γ 5 L7327 + (-1 : ℝ) * HLm Γ 5 L7329 + (-1 : ℝ) * HLm Γ 5 L660 := by
  have h := HLm_submod hΓ [F12] L661 [F67]
  rw [show [F12] ++ L661 ++ [F67] = L7330 from rfl, show [F12] ++ L661 = L7326 from rfl,
    show L661 ++ [F67] = L7328 from rfl] at h
  rw [i4344 hinj, i4342 hinj, i4343 hinj, i286 hinj] at h
  linarith

theorem row1538 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7331 + (1 : ℝ) * HLm Γ 5 L7332 + (-1 : ℝ) * HLm Γ 5 L4986 + (-1 : ℝ) * HLm Γ 5 L7333 := by
  have h := HLm_submod hΓ [F12] L7333 [F210]
  rw [show [F12] ++ L7333 ++ [F210] = L4986 from rfl, show [F12] ++ L7333 = L7331 from rfl,
    show L7333 ++ [F210] = L7332 from rfl] at h
  linarith

theorem row1539 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7334 + (1 : ℝ) * HLm Γ 5 L7336 + (-1 : ℝ) * HLm Γ 5 L7338 + (-1 : ℝ) * HLm Γ 5 L6790 := by
  have h := HLm_submod hΓ [F2] L6790 [F21]
  rw [show [F2] ++ L6790 ++ [F21] = L7339 from rfl, show [F2] ++ L6790 = L7335 from rfl,
    show L6790 ++ [F21] = L7337 from rfl] at h
  rw [i4347 hinj, i4345 hinj, i4346 hinj] at h
  linarith

theorem row1540 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4381 + (1 : ℝ) * HLm Γ 5 L3388 + (-1 : ℝ) * HLm Γ 5 L4059 + (-1 : ℝ) * HLm Γ 5 L3161 := by
  have h := HLm_submod hΓ [F2] L3161 [F210]
  rw [show [F2] ++ L3161 ++ [F210] = L7341 from rfl, show [F2] ++ L3161 = L7340 from rfl,
    show L3161 ++ [F210] = L3388 from rfl] at h
  rw [i4349 hinj, i4348 hinj] at h
  linarith

theorem row1541 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7123 + (1 : ℝ) * HLm Γ 5 L1143 + (-1 : ℝ) * HLm Γ 5 L4530 + (-1 : ℝ) * HLm Γ 5 L114 := by
  have h := HLm_submod hΓ [F210] L114 [F30]
  rw [show [F210] ++ L114 ++ [F30] = L7344 from rfl, show [F210] ++ L114 = L7342 from rfl,
    show L114 ++ [F30] = L7343 from rfl] at h
  rw [i4352 hinj, i4350 hinj, i4351 hinj] at h
  linarith

theorem row1542 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2899 + (1 : ℝ) * HLm Γ 5 L7345 + (-1 : ℝ) * HLm Γ 5 L7136 + (-1 : ℝ) * HLm Γ 5 L2872 := by
  have h := HLm_submod hΓ [F0] L2872 [F3]
  rw [show [F0] ++ L2872 ++ [F3] = L7347 from rfl, show [F0] ++ L2872 = L2899 from rfl,
    show L2872 ++ [F3] = L7346 from rfl] at h
  rw [i4354 hinj, i4353 hinj] at h
  linarith

theorem row1543 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7348 + (1 : ℝ) * HLm Γ 5 L3427 + (-1 : ℝ) * HLm Γ 5 L3431 + (-1 : ℝ) * HLm Γ 5 L7351 := by
  have h := HLm_submod hΓ [F236] L7351 [F27]
  rw [show [F236] ++ L7351 ++ [F27] = L7350 from rfl, show [F236] ++ L7351 = L7348 from rfl,
    show L7351 ++ [F27] = L7349 from rfl] at h
  rw [i4356 hinj, i4355 hinj] at h
  linarith

theorem row1544 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7352 + (1 : ℝ) * HLm Γ 5 L7354 + (-1 : ℝ) * HLm Γ 5 L7356 + (-1 : ℝ) * HLm Γ 5 L7358 := by
  have h := HLm_submod hΓ [F210] L7359 [F27]
  rw [show [F210] ++ L7359 ++ [F27] = L7357 from rfl, show [F210] ++ L7359 = L7353 from rfl,
    show L7359 ++ [F27] = L7355 from rfl] at h
  rw [i4359 hinj, i4357 hinj, i4358 hinj, i4360 hinj] at h
  linarith

theorem row1545 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7360 + (1 : ℝ) * HLm Γ 5 L3167 + (-1 : ℝ) * HLm Γ 5 L7362 + (-1 : ℝ) * HLm Γ 5 L7364 := by
  have h := HLm_submod hΓ [F0] L7365 [F43]
  rw [show [F0] ++ L7365 ++ [F43] = L7363 from rfl, show [F0] ++ L7365 = L7361 from rfl,
    show L7365 ++ [F43] = L4040 from rfl] at h
  rw [i4362 hinj, i4361 hinj, i2254 hinj, i4363 hinj] at h
  linarith

theorem row1546 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L897 + (1 : ℝ) * HLm Γ 5 L6960 + (-1 : ℝ) * HLm Γ 5 L3769 + (-1 : ℝ) * HLm Γ 5 L265 := by
  have h := HLm_submod hΓ [F7] L266 [F217]
  rw [show [F7] ++ L266 ++ [F217] = L7367 from rfl, show [F7] ++ L266 = L7366 from rfl,
    show L266 ++ [F217] = L6961 from rfl] at h
  rw [i4365 hinj, i4364 hinj, i4135 hinj, i99 hinj] at h
  linarith

theorem row1547 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3413 + (1 : ℝ) * HLm Γ 5 L6960 + (-1 : ℝ) * HLm Γ 5 L7369 + (-1 : ℝ) * HLm Γ 5 L265 := by
  have h := HLm_submod hΓ [F51] L266 [F217]
  rw [show [F51] ++ L266 ++ [F217] = L7370 from rfl, show [F51] ++ L266 = L7368 from rfl,
    show L266 ++ [F217] = L6961 from rfl] at h
  rw [i4367 hinj, i4366 hinj, i4135 hinj, i99 hinj] at h
  linarith

theorem row1548 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7371 + (1 : ℝ) * HLm Γ 5 L7373 + (-1 : ℝ) * HLm Γ 5 L7375 + (-1 : ℝ) * HLm Γ 5 L3159 := by
  have h := HLm_submod hΓ [F210] L3164 [F17]
  rw [show [F210] ++ L3164 ++ [F17] = L7376 from rfl, show [F210] ++ L3164 = L7372 from rfl,
    show L3164 ++ [F17] = L7374 from rfl] at h
  rw [i4370 hinj, i4368 hinj, i4369 hinj, i1790 hinj] at h
  linarith

theorem row1549 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3733 + (1 : ℝ) * HLm Γ 5 L7378 + (-1 : ℝ) * HLm Γ 5 L2891 + (-1 : ℝ) * HLm Γ 5 L6815 := by
  have h := HLm_submod hΓ [F1] L6816 [F0]
  rw [show [F1] ++ L6816 ++ [F0] = L7380 from rfl, show [F1] ++ L6816 = L7377 from rfl,
    show L6816 ++ [F0] = L7379 from rfl] at h
  rw [i4373 hinj, i4371 hinj, i4372 hinj, i4061 hinj] at h
  linarith

theorem row1550 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7381 + (1 : ℝ) * HLm Γ 5 L4642 + (-1 : ℝ) * HLm Γ 5 L7383 + (-1 : ℝ) * HLm Γ 5 L705 := by
  have h := HLm_submod hΓ [F210] L706 [F45]
  rw [show [F210] ++ L706 ++ [F45] = L7384 from rfl, show [F210] ++ L706 = L7382 from rfl,
    show L706 ++ [F45] = L4643 from rfl] at h
  rw [i4375 hinj, i4374 hinj, i2608 hinj, i309 hinj] at h
  linarith

theorem row1551 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7385 + (1 : ℝ) * HLm Γ 5 L4642 + (-1 : ℝ) * HLm Γ 5 L7387 + (-1 : ℝ) * HLm Γ 5 L705 := by
  have h := HLm_submod hΓ [F211] L706 [F45]
  rw [show [F211] ++ L706 ++ [F45] = L7388 from rfl, show [F211] ++ L706 = L7386 from rfl,
    show L706 ++ [F45] = L4643 from rfl] at h
  rw [i4377 hinj, i4376 hinj, i2608 hinj, i309 hinj] at h
  linarith

theorem row1552 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7389 + (1 : ℝ) * HLm Γ 5 L6822 + (-1 : ℝ) * HLm Γ 5 L7391 + (-1 : ℝ) * HLm Γ 5 L131 := by
  have h := HLm_submod hΓ [F17] L131 [F217]
  rw [show [F17] ++ L131 ++ [F217] = L7392 from rfl, show [F17] ++ L131 = L7390 from rfl,
    show L131 ++ [F217] = L6822 from rfl] at h
  rw [i4379 hinj, i4378 hinj] at h
  linarith

theorem row1553 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7393 + (1 : ℝ) * HLm Γ 5 L7395 + (-1 : ℝ) * HLm Γ 5 L7397 + (-1 : ℝ) * HLm Γ 5 L3105 := by
  have h := HLm_submod hΓ [F86] L3105 [F218]
  rw [show [F86] ++ L3105 ++ [F218] = L7398 from rfl, show [F86] ++ L3105 = L7394 from rfl,
    show L3105 ++ [F218] = L7396 from rfl] at h
  rw [i4382 hinj, i4380 hinj, i4381 hinj] at h
  linarith

theorem row1554 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7399 + (1 : ℝ) * HLm Γ 5 L6828 + (-1 : ℝ) * HLm Γ 5 L7402 + (-1 : ℝ) * HLm Γ 5 L6826 := by
  have h := HLm_submod hΓ [F7] L7404 [F6]
  rw [show [F7] ++ L7404 ++ [F6] = L7403 from rfl, show [F7] ++ L7404 = L7400 from rfl,
    show L7404 ++ [F6] = L7401 from rfl] at h
  rw [i4385 hinj, i4383 hinj, i4384 hinj, i4386 hinj] at h
  linarith

theorem row1555 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7405 + (1 : ℝ) * HLm Γ 5 L7407 + (-1 : ℝ) * HLm Γ 5 L7409 + (-1 : ℝ) * HLm Γ 5 L6830 := by
  have h := HLm_submod hΓ [F67] L7411 [F36]
  rw [show [F67] ++ L7411 ++ [F36] = L7410 from rfl, show [F67] ++ L7411 = L7406 from rfl,
    show L7411 ++ [F36] = L7408 from rfl] at h
  rw [i4389 hinj, i4387 hinj, i4388 hinj, i4390 hinj] at h
  linarith

theorem row1556 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6824 + (1 : ℝ) * HLm Γ 5 L7412 + (-1 : ℝ) * HLm Γ 5 L7414 + (-1 : ℝ) * HLm Γ 5 L2883 := by
  have h := HLm_submod hΓ [F16] L2883 [F82]
  rw [show [F16] ++ L2883 ++ [F82] = L7415 from rfl, show [F16] ++ L2883 = L6825 from rfl,
    show L2883 ++ [F82] = L7413 from rfl] at h
  rw [i4392 hinj, i4065 hinj, i4391 hinj] at h
  linarith

theorem row1557 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7416 + (1 : ℝ) * HLm Γ 5 L7418 + (-1 : ℝ) * HLm Γ 5 L7419 + (-1 : ℝ) * HLm Γ 5 L2003 := by
  have h := HLm_submod hΓ [F0] L2003 [F210]
  rw [show [F0] ++ L2003 ++ [F210] = L7420 from rfl, show [F0] ++ L2003 = L7417 from rfl,
    show L2003 ++ [F210] = L7418 from rfl] at h
  rw [i4394 hinj, i4393 hinj] at h
  linarith

theorem row1558 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7421 + (1 : ℝ) * HLm Γ 5 L7423 + (-1 : ℝ) * HLm Γ 5 L5969 + (-1 : ℝ) * HLm Γ 5 L6868 := by
  have h := HLm_submod hΓ [F16] L6869 [F23]
  rw [show [F16] ++ L6869 ++ [F23] = L7425 from rfl, show [F16] ++ L6869 = L7422 from rfl,
    show L6869 ++ [F23] = L7424 from rfl] at h
  rw [i4397 hinj, i4395 hinj, i4396 hinj, i4086 hinj] at h
  linarith

theorem row1559 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1401 + (1 : ℝ) * HLm Γ 5 L7426 + (-1 : ℝ) * HLm Γ 5 L7428 + (-1 : ℝ) * HLm Γ 5 L3459 := by
  have h := HLm_submod hΓ [F7] L3460 [F218]
  rw [show [F7] ++ L3460 ++ [F218] = L7429 from rfl, show [F7] ++ L3460 = L1402 from rfl,
    show L3460 ++ [F218] = L7427 from rfl] at h
  rw [i4399 hinj, i702 hinj, i4398 hinj, i1941 hinj] at h
  linarith

theorem row1560 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7430 + (1 : ℝ) * HLm Γ 5 L3455 + (-1 : ℝ) * HLm Γ 5 L4680 + (-1 : ℝ) * HLm Γ 5 L3459 := by
  have h := HLm_submod hΓ [F210] L3460 [F6]
  rw [show [F210] ++ L3460 ++ [F6] = L4681 from rfl, show [F210] ++ L3460 = L7431 from rfl,
    show L3460 ++ [F6] = L3456 from rfl] at h
  rw [i2629 hinj, i4400 hinj, i1939 hinj, i1941 hinj] at h
  linarith

theorem row1561 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L555 + (1 : ℝ) * HLm Γ 5 L7433 + (-1 : ℝ) * HLm Γ 5 L7434 + (-1 : ℝ) * HLm Γ 5 L6895 := by
  have h := HLm_submod hΓ [F0] L6895 [F45]
  rw [show [F0] ++ L6895 ++ [F45] = L7435 from rfl, show [F0] ++ L6895 = L7432 from rfl,
    show L6895 ++ [F45] = L7433 from rfl] at h
  rw [i4402 hinj, i4401 hinj] at h
  linarith

theorem row1562 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7436 + (1 : ℝ) * HLm Γ 5 L6842 + (-1 : ℝ) * HLm Γ 5 L7439 + (-1 : ℝ) * HLm Γ 5 L6840 := by
  have h := HLm_submod hΓ [F7] L6840 [F85]
  rw [show [F7] ++ L6840 ++ [F85] = L7440 from rfl, show [F7] ++ L6840 = L7437 from rfl,
    show L6840 ++ [F85] = L7438 from rfl] at h
  rw [i4405 hinj, i4403 hinj, i4404 hinj] at h
  linarith

theorem row1563 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7441 + (1 : ℝ) * HLm Γ 5 L7443 + (-1 : ℝ) * HLm Γ 5 L7445 + (-1 : ℝ) * HLm Γ 5 L7447 := by
  have h := HLm_submod hΓ [F46] L7448 [F43]
  rw [show [F46] ++ L7448 ++ [F43] = L7446 from rfl, show [F46] ++ L7448 = L7442 from rfl,
    show L7448 ++ [F43] = L7444 from rfl] at h
  rw [i4408 hinj, i4406 hinj, i4407 hinj, i4409 hinj] at h
  linarith

theorem row1564 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7449 + (1 : ℝ) * HLm Γ 5 L7451 + (-1 : ℝ) * HLm Γ 5 L7453 + (-1 : ℝ) * HLm Γ 5 L6855 := by
  have h := HLm_submod hΓ [F67] L6855 [F36]
  rw [show [F67] ++ L6855 ++ [F36] = L7454 from rfl, show [F67] ++ L6855 = L7450 from rfl,
    show L6855 ++ [F36] = L7452 from rfl] at h
  rw [i4412 hinj, i4410 hinj, i4411 hinj] at h
  linarith

theorem row1565 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7455 + (1 : ℝ) * HLm Γ 5 L7457 + (-1 : ℝ) * HLm Γ 5 L7459 + (-1 : ℝ) * HLm Γ 5 L739 := by
  have h := HLm_submod hΓ [F214] L740 [F45]
  rw [show [F214] ++ L740 ++ [F45] = L7460 from rfl, show [F214] ++ L740 = L7456 from rfl,
    show L740 ++ [F45] = L7458 from rfl] at h
  rw [i4415 hinj, i4413 hinj, i4414 hinj, i325 hinj] at h
  linarith

theorem row1566 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7461 + (1 : ℝ) * HLm Γ 5 L7463 + (-1 : ℝ) * HLm Γ 5 L7465 + (-1 : ℝ) * HLm Γ 5 L6836 := by
  have h := HLm_submod hΓ [F46] L6837 [F52]
  rw [show [F46] ++ L6837 ++ [F52] = L7466 from rfl, show [F46] ++ L6837 = L7462 from rfl,
    show L6837 ++ [F52] = L7464 from rfl] at h
  rw [i4418 hinj, i4416 hinj, i4417 hinj, i4071 hinj] at h
  linarith

theorem row1567 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6838 + (1 : ℝ) * HLm Γ 5 L7467 + (-1 : ℝ) * HLm Γ 5 L7469 + (-1 : ℝ) * HLm Γ 5 L6836 := by
  have h := HLm_submod hΓ [F67] L6837 [F34]
  rw [show [F67] ++ L6837 ++ [F34] = L7470 from rfl, show [F67] ++ L6837 = L6839 from rfl,
    show L6837 ++ [F34] = L7468 from rfl] at h
  rw [i4420 hinj, i4072 hinj, i4419 hinj, i4071 hinj] at h
  linarith

theorem row1568 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7471 + (1 : ℝ) * HLm Γ 5 L7473 + (-1 : ℝ) * HLm Γ 5 L7475 + (-1 : ℝ) * HLm Γ 5 L6836 := by
  have h := HLm_submod hΓ [F210] L6837 [F6]
  rw [show [F210] ++ L6837 ++ [F6] = L7476 from rfl, show [F210] ++ L6837 = L7472 from rfl,
    show L6837 ++ [F6] = L7474 from rfl] at h
  rw [i4423 hinj, i4421 hinj, i4422 hinj, i4071 hinj] at h
  linarith

theorem row1569 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6819 + (1 : ℝ) * HLm Γ 5 L7478 + (-1 : ℝ) * HLm Γ 5 L3447 + (-1 : ℝ) * HLm Γ 5 L2004 := by
  have h := HLm_submod hΓ [F0] L2004 [F16]
  rw [show [F0] ++ L2004 ++ [F16] = L7480 from rfl, show [F0] ++ L2004 = L7477 from rfl,
    show L2004 ++ [F16] = L7479 from rfl] at h
  rw [i4426 hinj, i4424 hinj, i4425 hinj] at h
  linarith

theorem row1570 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7478 + (1 : ℝ) * HLm Γ 5 L7482 + (-1 : ℝ) * HLm Γ 5 L7484 + (-1 : ℝ) * HLm Γ 5 L2004 := by
  have h := HLm_submod hΓ [F16] L2004 [F25]
  rw [show [F16] ++ L2004 ++ [F25] = L7485 from rfl, show [F16] ++ L2004 = L7481 from rfl,
    show L2004 ++ [F25] = L7483 from rfl] at h
  rw [i4429 hinj, i4427 hinj, i4428 hinj] at h
  linarith

theorem row1571 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7486 + (1 : ℝ) * HLm Γ 5 L7488 + (-1 : ℝ) * HLm Γ 5 L7490 + (-1 : ℝ) * HLm Γ 5 L2004 := by
  have h := HLm_submod hΓ [F22] L2004 [F214]
  rw [show [F22] ++ L2004 ++ [F214] = L7491 from rfl, show [F22] ++ L2004 = L7487 from rfl,
    show L2004 ++ [F214] = L7489 from rfl] at h
  rw [i4432 hinj, i4430 hinj, i4431 hinj] at h
  linarith

theorem row1572 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6896 + (1 : ℝ) * HLm Γ 5 L4711 + (-1 : ℝ) * HLm Γ 5 L7494 + (-1 : ℝ) * HLm Γ 5 L2837 := by
  have h := HLm_submod hΓ [F44] L2837 [F16]
  rw [show [F44] ++ L2837 ++ [F16] = L7495 from rfl, show [F44] ++ L2837 = L7492 from rfl,
    show L2837 ++ [F16] = L7493 from rfl] at h
  rw [i4435 hinj, i4433 hinj, i4434 hinj] at h
  linarith

theorem row1573 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6853 + (1 : ℝ) * HLm Γ 5 L3491 + (-1 : ℝ) * HLm Γ 5 L3493 + (-1 : ℝ) * HLm Γ 5 L6852 := by
  have h := HLm_submod hΓ [F210] L6852 [F34]
  rw [show [F210] ++ L6852 ++ [F34] = L7497 from rfl, show [F210] ++ L6852 = L6854 from rfl,
    show L6852 ++ [F34] = L7496 from rfl] at h
  rw [i4437 hinj, i4079 hinj, i4436 hinj] at h
  linarith

theorem row1574 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6906 + (1 : ℝ) * HLm Γ 5 L3463 + (-1 : ℝ) * HLm Γ 5 L7500 + (-1 : ℝ) * HLm Γ 5 L7502 := by
  have h := HLm_submod hΓ [F46] L7503 [F21]
  rw [show [F46] ++ L7503 ++ [F21] = L7501 from rfl, show [F46] ++ L7503 = L7498 from rfl,
    show L7503 ++ [F21] = L7499 from rfl] at h
  rw [i4440 hinj, i4438 hinj, i4439 hinj, i4441 hinj] at h
  linarith

theorem row1575 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7504 + (1 : ℝ) * HLm Γ 5 L2296 + (-1 : ℝ) * HLm Γ 5 L7506 + (-1 : ℝ) * HLm Γ 5 L2014 := by
  have h := HLm_submod hΓ [F21] L2014 [F23]
  rw [show [F21] ++ L2014 ++ [F23] = L7507 from rfl, show [F21] ++ L2014 = L7505 from rfl,
    show L2014 ++ [F23] = L2297 from rfl] at h
  rw [i4443 hinj, i4442 hinj, i1267 hinj] at h
  linarith

theorem row1576 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L796 + (1 : ℝ) * HLm Γ 5 L7509 + (-1 : ℝ) * HLm Γ 5 L7511 + (-1 : ℝ) * HLm Γ 5 L307 := by
  have h := HLm_submod hΓ [F67] L307 [F214]
  rw [show [F67] ++ L307 ++ [F214] = L7512 from rfl, show [F67] ++ L307 = L7508 from rfl,
    show L307 ++ [F214] = L7510 from rfl] at h
  rw [i4446 hinj, i4444 hinj, i4445 hinj] at h
  linarith

theorem row1577 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1960 + (1 : ℝ) * HLm Γ 5 L7099 + (-1 : ℝ) * HLm Γ 5 L7514 + (-1 : ℝ) * HLm Γ 5 L2305 := by
  have h := HLm_submod hΓ [F0] L2305 [F217]
  rw [show [F0] ++ L2305 ++ [F217] = L7515 from rfl, show [F0] ++ L2305 = L2300 from rfl,
    show L2305 ++ [F217] = L7513 from rfl] at h
  rw [i4448 hinj, i1269 hinj, i4447 hinj] at h
  linarith

theorem row1578 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3558 + (1 : ℝ) * HLm Γ 5 L7516 + (-1 : ℝ) * HLm Γ 5 L7518 + (-1 : ℝ) * HLm Γ 5 L25 := by
  have h := HLm_submod hΓ [F2] L25 [F218]
  rw [show [F2] ++ L25 ++ [F218] = L7519 from rfl, show [F2] ++ L25 = L3559 from rfl,
    show L25 ++ [F218] = L7517 from rfl] at h
  rw [i4450 hinj, i1994 hinj, i4449 hinj] at h
  linarith

theorem row1579 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3560 + (1 : ℝ) * HLm Γ 5 L7521 + (-1 : ℝ) * HLm Γ 5 L7523 + (-1 : ℝ) * HLm Γ 5 L25 := by
  have h := HLm_submod hΓ [F52] L25 [F236]
  rw [show [F52] ++ L25 ++ [F236] = L7524 from rfl, show [F52] ++ L25 = L7520 from rfl,
    show L25 ++ [F236] = L7522 from rfl] at h
  rw [i4453 hinj, i4451 hinj, i4452 hinj] at h
  linarith

theorem row1580 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3563 + (1 : ℝ) * HLm Γ 5 L7526 + (-1 : ℝ) * HLm Γ 5 L1458 + (-1 : ℝ) * HLm Γ 5 L7529 := by
  have h := HLm_submod hΓ [F0] L7530 [F96]
  rw [show [F0] ++ L7530 ++ [F96] = L7528 from rfl, show [F0] ++ L7530 = L7525 from rfl,
    show L7530 ++ [F96] = L7527 from rfl] at h
  rw [i4456 hinj, i4454 hinj, i4455 hinj, i4457 hinj] at h
  linarith

theorem row1581 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7531 + (1 : ℝ) * HLm Γ 5 L6878 + (-1 : ℝ) * HLm Γ 5 L7533 + (-1 : ℝ) * HLm Γ 5 L6876 := by
  have h := HLm_submod hΓ [F0] L6876 [F6]
  rw [show [F0] ++ L6876 ++ [F6] = L7534 from rfl, show [F0] ++ L6876 = L7532 from rfl,
    show L6876 ++ [F6] = L6878 from rfl] at h
  rw [i4459 hinj, i4458 hinj] at h
  linarith

theorem row1582 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7535 + (1 : ℝ) * HLm Γ 5 L7537 + (-1 : ℝ) * HLm Γ 5 L7539 + (-1 : ℝ) * HLm Γ 5 L7001 := by
  have h := HLm_submod hΓ [F52] L7002 [F214]
  rw [show [F52] ++ L7002 ++ [F214] = L7540 from rfl, show [F52] ++ L7002 = L7536 from rfl,
    show L7002 ++ [F214] = L7538 from rfl] at h
  rw [i4462 hinj, i4460 hinj, i4461 hinj, i4158 hinj] at h
  linarith

theorem row1583 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7541 + (1 : ℝ) * HLm Γ 5 L7543 + (-1 : ℝ) * HLm Γ 5 L7545 + (-1 : ℝ) * HLm Γ 5 L382 := by
  have h := HLm_submod hΓ [F1] L383 [F218]
  rw [show [F1] ++ L383 ++ [F218] = L7546 from rfl, show [F1] ++ L383 = L7542 from rfl,
    show L383 ++ [F218] = L7544 from rfl] at h
  rw [i4465 hinj, i4463 hinj, i4464 hinj, i154 hinj] at h
  linarith

theorem row1584 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L74 + (1 : ℝ) * HLm Γ 5 L7547 + (-1 : ℝ) * HLm Γ 5 L7306 + (-1 : ℝ) * HLm Γ 5 L2327 := by
  have h := HLm_submod hΓ [F0] L2328 [F43]
  rw [show [F0] ++ L2328 ++ [F43] = L7549 from rfl, show [F0] ++ L2328 = L3566 from rfl,
    show L2328 ++ [F43] = L7548 from rfl] at h
  rw [i4467 hinj, i1999 hinj, i4466 hinj, i1283 hinj] at h
  linarith

theorem row1585 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3003 + (1 : ℝ) * HLm Γ 5 L786 + (-1 : ℝ) * HLm Γ 5 L4869 + (-1 : ℝ) * HLm Γ 5 L155 := by
  have h := HLm_submod hΓ [F68] L156 [F96]
  rw [show [F68] ++ L156 ++ [F96] = L7551 from rfl, show [F68] ++ L156 = L7550 from rfl,
    show L156 ++ [F96] = L787 from rfl] at h
  rw [i4469 hinj, i4468 hinj, i351 hinj, i50 hinj] at h
  linarith

theorem row1586 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6860 + (1 : ℝ) * HLm Γ 5 L7103 + (-1 : ℝ) * HLm Γ 5 L7552 + (-1 : ℝ) * HLm Γ 5 L6859 := by
  have h := HLm_submod hΓ [F0] L6859 [F5]
  rw [show [F0] ++ L6859 ++ [F5] = L7553 from rfl, show [F0] ++ L6859 = L6861 from rfl,
    show L6859 ++ [F5] = L7104 from rfl] at h
  rw [i4470 hinj, i4082 hinj, i4214 hinj] at h
  linarith

theorem row1587 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6870 + (1 : ℝ) * HLm Γ 5 L3792 + (-1 : ℝ) * HLm Γ 5 L7555 + (-1 : ℝ) * HLm Γ 5 L6859 := by
  have h := HLm_submod hΓ [F47] L6859 [F16]
  rw [show [F47] ++ L6859 ++ [F16] = L7556 from rfl, show [F47] ++ L6859 = L6871 from rfl,
    show L6859 ++ [F16] = L7554 from rfl] at h
  rw [i4472 hinj, i4087 hinj, i4471 hinj] at h
  linarith

theorem row1588 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1594 + (1 : ℝ) * HLm Γ 5 L4041 + (-1 : ℝ) * HLm Γ 5 L7559 + (-1 : ℝ) * HLm Γ 5 L526 := by
  have h := HLm_submod hΓ [F5] L526 [F211]
  rw [show [F5] ++ L526 ++ [F211] = L7560 from rfl, show [F5] ++ L526 = L7557 from rfl,
    show L526 ++ [F211] = L7558 from rfl] at h
  rw [i4475 hinj, i4473 hinj, i4474 hinj] at h
  linarith

theorem row1589 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7561 + (1 : ℝ) * HLm Γ 5 L6874 + (-1 : ℝ) * HLm Γ 5 L7563 + (-1 : ℝ) * HLm Γ 5 L827 := by
  have h := HLm_submod hΓ [F21] L827 [F210]
  rw [show [F21] ++ L827 ++ [F210] = L7564 from rfl, show [F21] ++ L827 = L7562 from rfl,
    show L827 ++ [F210] = L6874 from rfl] at h
  rw [i4477 hinj, i4476 hinj] at h
  linarith

theorem row1590 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2839 + (1 : ℝ) * HLm Γ 5 L6886 + (-1 : ℝ) * HLm Γ 5 L7566 + (-1 : ℝ) * HLm Γ 5 L2901 := by
  have h := HLm_submod hΓ [F0] L2901 [F3]
  rw [show [F0] ++ L2901 ++ [F3] = L7567 from rfl, show [F0] ++ L2901 = L2902 from rfl,
    show L2901 ++ [F3] = L7565 from rfl] at h
  rw [i4479 hinj, i1656 hinj, i4478 hinj] at h
  linarith

theorem row1591 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7568 + (1 : ℝ) * HLm Γ 5 L4172 + (-1 : ℝ) * HLm Γ 5 L7570 + (-1 : ℝ) * HLm Γ 5 L421 := by
  have h := HLm_submod hΓ [F47] L872 [F218]
  rw [show [F47] ++ L872 ++ [F218] = L7571 from rfl, show [F47] ++ L872 = L7569 from rfl,
    show L872 ++ [F218] = L4978 from rfl] at h
  rw [i4481 hinj, i4480 hinj, i2806 hinj, i397 hinj] at h
  linarith

theorem row1592 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7572 + (1 : ℝ) * HLm Γ 5 L3654 + (-1 : ℝ) * HLm Γ 5 L7574 + (-1 : ℝ) * HLm Γ 5 L7576 := by
  have h := HLm_submod hΓ [F25] L7576 [F45]
  rw [show [F25] ++ L7576 ++ [F45] = L7575 from rfl, show [F25] ++ L7576 = L7573 from rfl,
    show L7576 ++ [F45] = L3654 from rfl] at h
  rw [i4483 hinj, i4482 hinj] at h
  linarith

theorem row1593 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7577 + (1 : ℝ) * HLm Γ 5 L7579 + (-1 : ℝ) * HLm Γ 5 L7581 + (-1 : ℝ) * HLm Γ 5 L2910 := by
  have h := HLm_submod hΓ [F16] L2910 [F17]
  rw [show [F16] ++ L2910 ++ [F17] = L7582 from rfl, show [F16] ++ L2910 = L7578 from rfl,
    show L2910 ++ [F17] = L7580 from rfl] at h
  rw [i4486 hinj, i4484 hinj, i4485 hinj] at h
  linarith

theorem row1594 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7583 + (1 : ℝ) * HLm Γ 5 L7585 + (-1 : ℝ) * HLm Γ 5 L7587 + (-1 : ℝ) * HLm Γ 5 L2059 := by
  have h := HLm_submod hΓ [F210] L2060 [F6]
  rw [show [F210] ++ L2060 ++ [F6] = L7588 from rfl, show [F210] ++ L2060 = L7584 from rfl,
    show L2060 ++ [F6] = L7586 from rfl] at h
  rw [i4489 hinj, i4487 hinj, i4488 hinj, i1129 hinj] at h
  linarith

theorem row1595 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1506 + (1 : ℝ) * HLm Γ 5 L6977 + (-1 : ℝ) * HLm Γ 5 L7590 + (-1 : ℝ) * HLm Γ 5 L3032 := by
  have h := HLm_submod hΓ [F47] L3033 [F218]
  rw [show [F47] ++ L3033 ++ [F218] = L7591 from rfl, show [F47] ++ L3033 = L7589 from rfl,
    show L3033 ++ [F218] = L6978 from rfl] at h
  rw [i4491 hinj, i4490 hinj, i4144 hinj, i1724 hinj] at h
  linarith

theorem row1596 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L222 + (1 : ℝ) * HLm Γ 5 L7593 + (-1 : ℝ) * HLm Γ 5 L7595 + (-1 : ℝ) * HLm Γ 5 L360 := by
  have h := HLm_submod hΓ [F1] L2093 [F68]
  rw [show [F1] ++ L2093 ++ [F68] = L7596 from rfl, show [F1] ++ L2093 = L7592 from rfl,
    show L2093 ++ [F68] = L7594 from rfl] at h
  rw [i4494 hinj, i4492 hinj, i4493 hinj, i1148 hinj] at h
  linarith

theorem row1597 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7597 + (1 : ℝ) * HLm Γ 5 L3725 + (-1 : ℝ) * HLm Γ 5 L7599 + (-1 : ℝ) * HLm Γ 5 L2933 := by
  have h := HLm_submod hΓ [F7] L2934 [F236]
  rw [show [F7] ++ L2934 ++ [F236] = L7600 from rfl, show [F7] ++ L2934 = L7598 from rfl,
    show L2934 ++ [F236] = L3726 from rfl] at h
  rw [i4496 hinj, i4495 hinj, i2084 hinj, i1672 hinj] at h
  linarith

theorem row1598 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7115 + (1 : ℝ) * HLm Γ 5 L7602 + (-1 : ℝ) * HLm Γ 5 L7604 + (-1 : ℝ) * HLm Γ 5 L3179 := by
  have h := HLm_submod hΓ [F1] L6889 [F211]
  rw [show [F1] ++ L6889 ++ [F211] = L7605 from rfl, show [F1] ++ L6889 = L7601 from rfl,
    show L6889 ++ [F211] = L7603 from rfl] at h
  rw [i4499 hinj, i4497 hinj, i4498 hinj, i4099 hinj] at h
  linarith

theorem row1599 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7606 + (1 : ℝ) * HLm Γ 5 L7608 + (-1 : ℝ) * HLm Γ 5 L7610 + (-1 : ℝ) * HLm Γ 5 L3213 := by
  have h := HLm_submod hΓ [F7] L3214 [F108]
  rw [show [F7] ++ L3214 ++ [F108] = L7611 from rfl, show [F7] ++ L3214 = L7607 from rfl,
    show L3214 ++ [F108] = L7609 from rfl] at h
  rw [i4502 hinj, i4500 hinj, i4501 hinj, i1816 hinj] at h
  linarith

theorem row1600 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L218 + (1 : ℝ) * HLm Γ 5 L7613 + (-1 : ℝ) * HLm Γ 5 L2735 + (-1 : ℝ) * HLm Γ 5 L216 := by
  have h := HLm_submod hΓ [F67] L216 [F25]
  rw [show [F67] ++ L216 ++ [F25] = L7615 from rfl, show [F67] ++ L216 = L7612 from rfl,
    show L216 ++ [F25] = L7614 from rfl] at h
  rw [i4505 hinj, i4503 hinj, i4504 hinj] at h
  linarith

theorem row1601 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7616 + (1 : ℝ) * HLm Γ 5 L2978 + (-1 : ℝ) * HLm Γ 5 L7618 + (-1 : ℝ) * HLm Γ 5 L2974 := by
  have h := HLm_submod hΓ [F7] L2975 [F218]
  rw [show [F7] ++ L2975 ++ [F218] = L7619 from rfl, show [F7] ++ L2975 = L7617 from rfl,
    show L2975 ++ [F218] = L2979 from rfl] at h
  rw [i4507 hinj, i4506 hinj, i1698 hinj, i1696 hinj] at h
  linarith

theorem row1602 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7620 + (1 : ℝ) * HLm Γ 5 L2080 + (-1 : ℝ) * HLm Γ 5 L7622 + (-1 : ℝ) * HLm Γ 5 L2078 := by
  have h := HLm_submod hΓ [F228] L2079 [F45]
  rw [show [F228] ++ L2079 ++ [F45] = L7623 from rfl, show [F228] ++ L2079 = L7621 from rfl,
    show L2079 ++ [F45] = L2081 from rfl] at h
  rw [i4509 hinj, i4508 hinj, i1141 hinj, i1140 hinj] at h
  linarith

theorem row1603 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7624 + (1 : ℝ) * HLm Γ 5 L6988 + (-1 : ℝ) * HLm Γ 5 L1473 + (-1 : ℝ) * HLm Γ 5 L6986 := by
  have h := HLm_submod hΓ [F7] L6987 [F67]
  rw [show [F7] ++ L6987 ++ [F67] = L7626 from rfl, show [F7] ++ L6987 = L7625 from rfl,
    show L6987 ++ [F67] = L6989 from rfl] at h
  rw [i4511 hinj, i4510 hinj, i4151 hinj, i4150 hinj] at h
  linarith

theorem row1604 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7627 + (1 : ℝ) * HLm Γ 5 L6904 + (-1 : ℝ) * HLm Γ 5 L7630 + (-1 : ℝ) * HLm Γ 5 L6902 := by
  have h := HLm_submod hΓ [F67] L6903 [F25]
  rw [show [F67] ++ L6903 ++ [F25] = L7631 from rfl, show [F67] ++ L6903 = L7628 from rfl,
    show L6903 ++ [F25] = L7629 from rfl] at h
  rw [i4514 hinj, i4512 hinj, i4513 hinj, i4105 hinj] at h
  linarith

theorem row1605 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L218 + (1 : ℝ) * HLm Γ 5 L7633 + (-1 : ℝ) * HLm Γ 5 L7635 + (-1 : ℝ) * HLm Γ 5 L196 := by
  have h := HLm_submod hΓ [F16] L196 [F228]
  rw [show [F16] ++ L196 ++ [F228] = L7636 from rfl, show [F16] ++ L196 = L7632 from rfl,
    show L196 ++ [F228] = L7634 from rfl] at h
  rw [i4517 hinj, i4515 hinj, i4516 hinj] at h
  linarith

theorem row1606 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6891 + (1 : ℝ) * HLm Γ 5 L7637 + (-1 : ℝ) * HLm Γ 5 L7639 + (-1 : ℝ) * HLm Γ 5 L6890 := by
  have h := HLm_submod hΓ [F0] L6890 [F16]
  rw [show [F0] ++ L6890 ++ [F16] = L7640 from rfl, show [F0] ++ L6890 = L6891 from rfl,
    show L6890 ++ [F16] = L7638 from rfl] at h
  rw [i4519 hinj, i4518 hinj] at h
  linarith

theorem row1607 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7637 + (1 : ℝ) * HLm Γ 5 L7642 + (-1 : ℝ) * HLm Γ 5 L7644 + (-1 : ℝ) * HLm Γ 5 L6890 := by
  have h := HLm_submod hΓ [F16] L6890 [F17]
  rw [show [F16] ++ L6890 ++ [F17] = L7645 from rfl, show [F16] ++ L6890 = L7641 from rfl,
    show L6890 ++ [F17] = L7643 from rfl] at h
  rw [i4522 hinj, i4520 hinj, i4521 hinj] at h
  linarith

theorem row1608 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3753 + (1 : ℝ) * HLm Γ 5 L7646 + (-1 : ℝ) * HLm Γ 5 L7648 + (-1 : ℝ) * HLm Γ 5 L910 := by
  have h := HLm_submod hΓ [F67] L911 [F17]
  rw [show [F67] ++ L911 ++ [F17] = L7649 from rfl, show [F67] ++ L911 = L3754 from rfl,
    show L911 ++ [F17] = L7647 from rfl] at h
  rw [i4524 hinj, i2098 hinj, i4523 hinj, i418 hinj] at h
  linarith

theorem row1609 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7650 + (1 : ℝ) * HLm Γ 5 L924 + (-1 : ℝ) * HLm Γ 5 L7653 + (-1 : ℝ) * HLm Γ 5 L930 := by
  have h := HLm_submod hΓ [F21] L931 [F67]
  rw [show [F21] ++ L931 ++ [F67] = L7654 from rfl, show [F21] ++ L931 = L7651 from rfl,
    show L931 ++ [F67] = L7652 from rfl] at h
  rw [i4527 hinj, i4525 hinj, i4526 hinj, i428 hinj] at h
  linarith

theorem row1610 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L101 + (1 : ℝ) * HLm Γ 5 L2391 + (-1 : ℝ) * HLm Γ 5 L1317 + (-1 : ℝ) * HLm Γ 5 L2395 := by
  have h := HLm_submod hΓ [F0] L2395 [F16]
  rw [show [F0] ++ L2395 ++ [F16] = L7655 from rfl, show [F0] ++ L2395 = L101 from rfl,
    show L2395 ++ [F16] = L2392 from rfl] at h
  rw [i4528 hinj, i1316 hinj] at h
  linarith

theorem row1611 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6822 + (1 : ℝ) * HLm Γ 5 L7106 + (-1 : ℝ) * HLm Γ 5 L7656 + (-1 : ℝ) * HLm Γ 5 L2846 := by
  have h := HLm_submod hΓ [F51] L2846 [F16]
  rw [show [F51] ++ L2846 ++ [F16] = L7657 from rfl, show [F51] ++ L2846 = L6822 from rfl,
    show L2846 ++ [F16] = L7107 from rfl] at h
  rw [i4529 hinj, i4216 hinj] at h
  linarith

theorem row1612 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7658 + (1 : ℝ) * HLm Γ 5 L7660 + (-1 : ℝ) * HLm Γ 5 L7662 + (-1 : ℝ) * HLm Γ 5 L470 := by
  have h := HLm_submod hΓ [F2] L7664 [F228]
  rw [show [F2] ++ L7664 ++ [F228] = L7663 from rfl, show [F2] ++ L7664 = L7659 from rfl,
    show L7664 ++ [F228] = L7661 from rfl] at h
  rw [i4532 hinj, i4530 hinj, i4531 hinj, i4533 hinj] at h
  linarith

theorem row1613 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7665 + (1 : ℝ) * HLm Γ 5 L220 + (-1 : ℝ) * HLm Γ 5 L7668 + (-1 : ℝ) * HLm Γ 5 L40 := by
  have h := HLm_submod hΓ [F107] L41 [F67]
  rw [show [F107] ++ L41 ++ [F67] = L7669 from rfl, show [F107] ++ L41 = L7666 from rfl,
    show L41 ++ [F67] = L7667 from rfl] at h
  rw [i4536 hinj, i4534 hinj, i4535 hinj, i7 hinj] at h
  linarith

theorem row1614 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L454 + (1 : ℝ) * HLm Γ 5 L7671 + (-1 : ℝ) * HLm Γ 5 L7673 + (-1 : ℝ) * HLm Γ 5 L1968 := by
  have h := HLm_submod hΓ [F67] L1969 [F228]
  rw [show [F67] ++ L1969 ++ [F228] = L7674 from rfl, show [F67] ++ L1969 = L7670 from rfl,
    show L1969 ++ [F228] = L7672 from rfl] at h
  rw [i4539 hinj, i4537 hinj, i4538 hinj, i1085 hinj] at h
  linarith

theorem row1615 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7675 + (1 : ℝ) * HLm Γ 5 L2128 + (-1 : ℝ) * HLm Γ 5 L970 + (-1 : ℝ) * HLm Γ 5 L398 := by
  have h := HLm_submod hΓ [F0] L399 [F67]
  rw [show [F0] ++ L399 ++ [F67] = L7677 from rfl, show [F0] ++ L399 = L7676 from rfl,
    show L399 ++ [F67] = L2129 from rfl] at h
  rw [i4541 hinj, i4540 hinj, i1166 hinj, i160 hinj] at h
  linarith

theorem row1616 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7678 + (1 : ℝ) * HLm Γ 5 L7680 + (-1 : ℝ) * HLm Γ 5 L7682 + (-1 : ℝ) * HLm Γ 5 L7684 := by
  have h := HLm_submod hΓ [F96] L7685 [F217]
  rw [show [F96] ++ L7685 ++ [F217] = L7683 from rfl, show [F96] ++ L7685 = L7679 from rfl,
    show L7685 ++ [F217] = L7681 from rfl] at h
  rw [i4544 hinj, i4542 hinj, i4543 hinj, i4545 hinj] at h
  linarith

theorem row1617 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2666 + (1 : ℝ) * HLm Γ 5 L7686 + (-1 : ℝ) * HLm Γ 5 L7688 + (-1 : ℝ) * HLm Γ 5 L7690 := by
  have h := HLm_submod hΓ [F9] L7690 [F236]
  rw [show [F9] ++ L7690 ++ [F236] = L7689 from rfl, show [F9] ++ L7690 = L2667 from rfl,
    show L7690 ++ [F236] = L7687 from rfl] at h
  rw [i4547 hinj, i1498 hinj, i4546 hinj] at h
  linarith

theorem row1618 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L550 + (1 : ℝ) * HLm Γ 5 L7692 + (-1 : ℝ) * HLm Γ 5 L2219 + (-1 : ℝ) * HLm Γ 5 L965 := by
  have h := HLm_submod hΓ [F0] L966 [F23]
  rw [show [F0] ++ L966 ++ [F23] = L7694 from rfl, show [F0] ++ L966 = L7691 from rfl,
    show L966 ++ [F23] = L7693 from rfl] at h
  rw [i4550 hinj, i4548 hinj, i4549 hinj, i446 hinj] at h
  linarith

theorem row1619 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7695 + (1 : ℝ) * HLm Γ 5 L7697 + (-1 : ℝ) * HLm Γ 5 L7699 + (-1 : ℝ) * HLm Γ 5 L965 := by
  have h := HLm_submod hΓ [F210] L966 [F6]
  rw [show [F210] ++ L966 ++ [F6] = L7700 from rfl, show [F210] ++ L966 = L7696 from rfl,
    show L966 ++ [F6] = L7698 from rfl] at h
  rw [i4553 hinj, i4551 hinj, i4552 hinj, i446 hinj] at h
  linarith

theorem row1620 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7701 + (1 : ℝ) * HLm Γ 5 L7697 + (-1 : ℝ) * HLm Γ 5 L7703 + (-1 : ℝ) * HLm Γ 5 L965 := by
  have h := HLm_submod hΓ [F228] L966 [F6]
  rw [show [F228] ++ L966 ++ [F6] = L7704 from rfl, show [F228] ++ L966 = L7702 from rfl,
    show L966 ++ [F6] = L7698 from rfl] at h
  rw [i4555 hinj, i4554 hinj, i4552 hinj, i446 hinj] at h
  linarith

theorem row1621 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7705 + (1 : ℝ) * HLm Γ 5 L2404 + (-1 : ℝ) * HLm Γ 5 L7708 + (-1 : ℝ) * HLm Γ 5 L2084 := by
  have h := HLm_submod hΓ [F210] L2084 [F45]
  rw [show [F210] ++ L2084 ++ [F45] = L7709 from rfl, show [F210] ++ L2084 = L7706 from rfl,
    show L2084 ++ [F45] = L7707 from rfl] at h
  rw [i4558 hinj, i4556 hinj, i4557 hinj] at h
  linarith

theorem row1622 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7020 + (1 : ℝ) * HLm Γ 5 L7711 + (-1 : ℝ) * HLm Γ 5 L7712 + (-1 : ℝ) * HLm Γ 5 L7019 := by
  have h := HLm_submod hΓ [F67] L7019 [F210]
  rw [show [F67] ++ L7019 ++ [F210] = L7713 from rfl, show [F67] ++ L7019 = L7710 from rfl,
    show L7019 ++ [F210] = L7711 from rfl] at h
  rw [i4560 hinj, i4559 hinj] at h
  linarith

theorem row1623 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7714 + (1 : ℝ) * HLm Γ 5 L7716 + (-1 : ℝ) * HLm Γ 5 L7718 + (-1 : ℝ) * HLm Γ 5 L7720 := by
  have h := HLm_submod hΓ [F3] L7721 [F67]
  rw [show [F3] ++ L7721 ++ [F67] = L7719 from rfl, show [F3] ++ L7721 = L7715 from rfl,
    show L7721 ++ [F67] = L7717 from rfl] at h
  rw [i4563 hinj, i4561 hinj, i4562 hinj, i4564 hinj] at h
  linarith

theorem row1624 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2336 + (1 : ℝ) * HLm Γ 5 L7722 + (-1 : ℝ) * HLm Γ 5 L7724 + (-1 : ℝ) * HLm Γ 5 L3822 := by
  have h := HLm_submod hΓ [F9] L3822 [F3]
  rw [show [F9] ++ L3822 ++ [F3] = L7725 from rfl, show [F9] ++ L3822 = L2336 from rfl,
    show L3822 ++ [F3] = L7723 from rfl] at h
  rw [i4566 hinj, i4565 hinj] at h
  linarith

theorem row1625 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L118 + (1 : ℝ) * HLm Γ 5 L7727 + (-1 : ℝ) * HLm Γ 5 L7729 + (-1 : ℝ) * HLm Γ 5 L55 := by
  have h := HLm_submod hΓ [F7] L55 [F236]
  rw [show [F7] ++ L55 ++ [F236] = L7730 from rfl, show [F7] ++ L55 = L7726 from rfl,
    show L55 ++ [F236] = L7728 from rfl] at h
  rw [i4569 hinj, i4567 hinj, i4568 hinj] at h
  linarith

theorem row1626 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L516 + (1 : ℝ) * HLm Γ 5 L7732 + (-1 : ℝ) * HLm Γ 5 L7733 + (-1 : ℝ) * HLm Γ 5 L55 := by
  have h := HLm_submod hΓ [F46] L55 [F210]
  rw [show [F46] ++ L55 ++ [F210] = L7734 from rfl, show [F46] ++ L55 = L7731 from rfl,
    show L55 ++ [F210] = L7732 from rfl] at h
  rw [i4571 hinj, i4570 hinj] at h
  linarith

theorem row1627 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7735 + (1 : ℝ) * HLm Γ 5 L7737 + (-1 : ℝ) * HLm Γ 5 L7739 + (-1 : ℝ) * HLm Γ 5 L6922 := by
  have h := HLm_submod hΓ [F67] L7741 [F214]
  rw [show [F67] ++ L7741 ++ [F214] = L7740 from rfl, show [F67] ++ L7741 = L7736 from rfl,
    show L7741 ++ [F214] = L7738 from rfl] at h
  rw [i4574 hinj, i4572 hinj, i4573 hinj, i4575 hinj] at h
  linarith

theorem row1628 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7742 + (1 : ℝ) * HLm Γ 5 L7744 + (-1 : ℝ) * HLm Γ 5 L7746 + (-1 : ℝ) * HLm Γ 5 L6922 := by
  have h := HLm_submod hΓ [F228] L7741 [F45]
  rw [show [F228] ++ L7741 ++ [F45] = L7747 from rfl, show [F228] ++ L7741 = L7743 from rfl,
    show L7741 ++ [F45] = L7745 from rfl] at h
  rw [i4578 hinj, i4576 hinj, i4577 hinj, i4575 hinj] at h
  linarith

theorem row1629 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6920 + (1 : ℝ) * HLm Γ 5 L7748 + (-1 : ℝ) * HLm Γ 5 L7750 + (-1 : ℝ) * HLm Γ 5 L6918 := by
  have h := HLm_submod hΓ [F67] L6919 [F214]
  rw [show [F67] ++ L6919 ++ [F214] = L7751 from rfl, show [F67] ++ L6919 = L6921 from rfl,
    show L6919 ++ [F214] = L7749 from rfl] at h
  rw [i4580 hinj, i4116 hinj, i4579 hinj, i4115 hinj] at h
  linarith

theorem row1630 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7752 + (1 : ℝ) * HLm Γ 5 L7744 + (-1 : ℝ) * HLm Γ 5 L7755 + (-1 : ℝ) * HLm Γ 5 L7757 := by
  have h := HLm_submod hΓ [F214] L7758 [F17]
  rw [show [F214] ++ L7758 ++ [F17] = L7756 from rfl, show [F214] ++ L7758 = L7753 from rfl,
    show L7758 ++ [F17] = L7754 from rfl] at h
  rw [i4583 hinj, i4581 hinj, i4582 hinj, i4584 hinj] at h
  linarith

theorem row1631 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7759 + (1 : ℝ) * HLm Γ 5 L7110 + (-1 : ℝ) * HLm Γ 5 L7761 + (-1 : ℝ) * HLm Γ 5 L7101 := by
  have h := HLm_submod hΓ [F67] L7108 [F17]
  rw [show [F67] ++ L7108 ++ [F17] = L7762 from rfl, show [F67] ++ L7108 = L7760 from rfl,
    show L7108 ++ [F17] = L7111 from rfl] at h
  rw [i4586 hinj, i4585 hinj, i4219 hinj, i4217 hinj] at h
  linarith

theorem row1632 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7763 + (1 : ℝ) * HLm Γ 5 L7764 + (-1 : ℝ) * HLm Γ 5 L7766 + (-1 : ℝ) * HLm Γ 5 L2980 := by
  have h := HLm_submod hΓ [F25] L2980 [F85]
  rw [show [F25] ++ L2980 ++ [F85] = L7767 from rfl, show [F25] ++ L2980 = L7763 from rfl,
    show L2980 ++ [F85] = L7765 from rfl] at h
  rw [i4588 hinj, i4587 hinj] at h
  linarith

theorem row1633 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7768 + (1 : ℝ) * HLm Γ 5 L6967 + (-1 : ℝ) * HLm Γ 5 L7770 + (-1 : ℝ) * HLm Γ 5 L3015 := by
  have h := HLm_submod hΓ [F228] L3016 [F96]
  rw [show [F228] ++ L3016 ++ [F96] = L7771 from rfl, show [F228] ++ L3016 = L7769 from rfl,
    show L3016 ++ [F96] = L6968 from rfl] at h
  rw [i4590 hinj, i4589 hinj, i4139 hinj, i1716 hinj] at h
  linarith

theorem row1634 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7772 + (1 : ℝ) * HLm Γ 5 L6971 + (-1 : ℝ) * HLm Γ 5 L7774 + (-1 : ℝ) * HLm Γ 5 L3015 := by
  have h := HLm_submod hΓ [F214] L3016 [F85]
  rw [show [F214] ++ L3016 ++ [F85] = L7775 from rfl, show [F214] ++ L3016 = L7773 from rfl,
    show L3016 ++ [F85] = L6972 from rfl] at h
  rw [i4592 hinj, i4591 hinj, i4141 hinj, i1716 hinj] at h
  linarith

theorem row1635 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3236 + (1 : ℝ) * HLm Γ 5 L5207 + (-1 : ℝ) * HLm Γ 5 L7777 + (-1 : ℝ) * HLm Γ 5 L320 := by
  have h := HLm_submod hΓ [F0] L6990 [F236]
  rw [show [F0] ++ L6990 ++ [F236] = L7778 from rfl, show [F0] ++ L6990 = L7776 from rfl,
    show L6990 ++ [F236] = L6992 from rfl] at h
  rw [i4594 hinj, i4593 hinj, i4153 hinj, i4152 hinj] at h
  linarith

theorem row1636 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7779 + (1 : ℝ) * HLm Γ 5 L2094 + (-1 : ℝ) * HLm Γ 5 L4124 + (-1 : ℝ) * HLm Γ 5 L329 := by
  have h := HLm_submod hΓ [F62] L2982 [F3]
  rw [show [F62] ++ L2982 ++ [F3] = L7782 from rfl, show [F62] ++ L2982 = L7780 from rfl,
    show L2982 ++ [F3] = L7781 from rfl] at h
  rw [i4597 hinj, i4595 hinj, i4596 hinj, i1700 hinj] at h
  linarith

theorem row1637 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2094 + (1 : ℝ) * HLm Γ 5 L6929 + (-1 : ℝ) * HLm Γ 5 L7785 + (-1 : ℝ) * HLm Γ 5 L329 := by
  have h := HLm_submod hΓ [F3] L2982 [F228]
  rw [show [F3] ++ L2982 ++ [F228] = L7786 from rfl, show [F3] ++ L2982 = L7783 from rfl,
    show L2982 ++ [F228] = L7784 from rfl] at h
  rw [i4600 hinj, i4598 hinj, i4599 hinj, i1700 hinj] at h
  linarith

theorem row1638 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1175 + (1 : ℝ) * HLm Γ 5 L7788 + (-1 : ℝ) * HLm Γ 5 L7790 + (-1 : ℝ) * HLm Γ 5 L2126 := by
  have h := HLm_submod hΓ [F3] L2986 [F218]
  rw [show [F3] ++ L2986 ++ [F218] = L7791 from rfl, show [F3] ++ L2986 = L7787 from rfl,
    show L2986 ++ [F218] = L7789 from rfl] at h
  rw [i4603 hinj, i4601 hinj, i4602 hinj, i1702 hinj] at h
  linarith

theorem row1639 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7071 + (1 : ℝ) * HLm Γ 5 L3893 + (-1 : ℝ) * HLm Γ 5 L7793 + (-1 : ℝ) * HLm Γ 5 L2141 := by
  have h := HLm_submod hΓ [F12] L2142 [F228]
  rw [show [F12] ++ L2142 ++ [F228] = L7794 from rfl, show [F12] ++ L2142 = L7792 from rfl,
    show L2142 ++ [F228] = L3894 from rfl] at h
  rw [i4605 hinj, i4604 hinj, i2175 hinj, i1174 hinj] at h
  linarith

theorem row1640 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7795 + (1 : ℝ) * HLm Γ 5 L7797 + (-1 : ℝ) * HLm Γ 5 L7799 + (-1 : ℝ) * HLm Γ 5 L2992 := by
  have h := HLm_submod hΓ [F0] L2992 [F55]
  rw [show [F0] ++ L2992 ++ [F55] = L7800 from rfl, show [F0] ++ L2992 = L7796 from rfl,
    show L2992 ++ [F55] = L7798 from rfl] at h
  rw [i4608 hinj, i4606 hinj, i4607 hinj] at h
  linarith

theorem row1641 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7801 + (1 : ℝ) * HLm Γ 5 L7803 + (-1 : ℝ) * HLm Γ 5 L7805 + (-1 : ℝ) * HLm Γ 5 L3021 := by
  have h := HLm_submod hΓ [F210] L3022 [F96]
  rw [show [F210] ++ L3022 ++ [F96] = L7806 from rfl, show [F210] ++ L3022 = L7802 from rfl,
    show L3022 ++ [F96] = L7804 from rfl] at h
  rw [i4611 hinj, i4609 hinj, i4610 hinj, i1719 hinj] at h
  linarith

theorem row1642 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7807 + (1 : ℝ) * HLm Γ 5 L7809 + (-1 : ℝ) * HLm Γ 5 L7810 + (-1 : ℝ) * HLm Γ 5 L400 := by
  have h := HLm_submod hΓ [F2] L400 [F210]
  rw [show [F2] ++ L400 ++ [F210] = L7811 from rfl, show [F2] ++ L400 = L7808 from rfl,
    show L400 ++ [F210] = L7809 from rfl] at h
  rw [i4613 hinj, i4612 hinj] at h
  linarith

theorem row1643 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7812 + (1 : ℝ) * HLm Γ 5 L7814 + (-1 : ℝ) * HLm Γ 5 L7815 + (-1 : ℝ) * HLm Γ 5 L7817 := by
  have h := HLm_submod hΓ [F1] L7817 [F210]
  rw [show [F1] ++ L7817 ++ [F210] = L7816 from rfl, show [F1] ++ L7817 = L7813 from rfl,
    show L7817 ++ [F210] = L7814 from rfl] at h
  rw [i4615 hinj, i4614 hinj] at h
  linarith

theorem row1644 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7818 + (1 : ℝ) * HLm Γ 5 L7064 + (-1 : ℝ) * HLm Γ 5 L7820 + (-1 : ℝ) * HLm Γ 5 L7060 := by
  have h := HLm_submod hΓ [F7] L7061 [F214]
  rw [show [F7] ++ L7061 ++ [F214] = L7821 from rfl, show [F7] ++ L7061 = L7819 from rfl,
    show L7061 ++ [F214] = L7065 from rfl] at h
  rw [i4617 hinj, i4616 hinj, i4190 hinj, i4188 hinj] at h
  linarith

theorem row1645 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7822 + (1 : ℝ) * HLm Γ 5 L7095 + (-1 : ℝ) * HLm Γ 5 L7825 + (-1 : ℝ) * HLm Γ 5 L2147 := by
  have h := HLm_submod hΓ [F211] L2148 [F36]
  rw [show [F211] ++ L2148 ++ [F36] = L7826 from rfl, show [F211] ++ L2148 = L7823 from rfl,
    show L2148 ++ [F36] = L7824 from rfl] at h
  rw [i4620 hinj, i4618 hinj, i4619 hinj, i1177 hinj] at h
  linarith

theorem row1646 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7827 + (1 : ℝ) * HLm Γ 5 L3933 + (-1 : ℝ) * HLm Γ 5 L7829 + (-1 : ℝ) * HLm Γ 5 L3937 := by
  have h := HLm_submod hΓ [F1] L3938 [F211]
  rw [show [F1] ++ L3938 ++ [F211] = L7830 from rfl, show [F1] ++ L3938 = L7828 from rfl,
    show L3938 ++ [F211] = L3934 from rfl] at h
  rw [i4622 hinj, i4621 hinj, i2196 hinj, i2198 hinj] at h
  linarith

theorem row1647 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L656 + (1 : ℝ) * HLm Γ 5 L3931 + (-1 : ℝ) * HLm Γ 5 L7833 + (-1 : ℝ) * HLm Γ 5 L3937 := by
  have h := HLm_submod hΓ [F7] L3938 [F2]
  rw [show [F7] ++ L3938 ++ [F2] = L7834 from rfl, show [F7] ++ L3938 = L7831 from rfl,
    show L3938 ++ [F2] = L7832 from rfl] at h
  rw [i4625 hinj, i4623 hinj, i4624 hinj, i2198 hinj] at h
  linarith

theorem row1648 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L7835 + (1 : ℝ) * HLm Γ 5 L7837 + (-1 : ℝ) * HLm Γ 5 L4628 + (-1 : ℝ) * HLm Γ 5 L7840 := by
  have h := HLm_submod hΓ [F2] L7840 [F27]
  rw [show [F2] ++ L7840 ++ [F27] = L7839 from rfl, show [F2] ++ L7840 = L7836 from rfl,
    show L7840 ++ [F27] = L7838 from rfl] at h
  rw [i4628 hinj, i4626 hinj, i4627 hinj] at h
  linarith

theorem row1649 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6979 + (1 : ℝ) * HLm Γ 5 L7842 + (-1 : ℝ) * HLm Γ 5 L7844 + (-1 : ℝ) * HLm Γ 5 L309 := by
  have h := HLm_submod hΓ [F1] L3951 [F228]
  rw [show [F1] ++ L3951 ++ [F228] = L7845 from rfl, show [F1] ++ L3951 = L7841 from rfl,
    show L3951 ++ [F228] = L7843 from rfl] at h
  rw [i4631 hinj, i4629 hinj, i4630 hinj, i2205 hinj] at h
  linarith

end EntropyBounds.TwoSet.Certs.R7A5
