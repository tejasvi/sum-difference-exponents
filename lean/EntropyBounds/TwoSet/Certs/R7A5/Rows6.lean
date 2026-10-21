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

theorem row900 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4232 + (1 : ℝ) * HLm Γ 5 L3269 + (-1 : ℝ) * HLm Γ 5 L4235 + (-1 : ℝ) * HLm Γ 5 L3224 := by
  have h := HLm_submod hΓ [F107] L4237 [F45]
  rw [show [F107] ++ L4237 ++ [F45] = L4236 from rfl, show [F107] ++ L4237 = L4233 from rfl,
    show L4237 ++ [F45] = L4234 from rfl] at h
  rw [i2367 hinj, i2365 hinj, i2366 hinj, i2368 hinj] at h
  linarith

theorem row901 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4221 + (1 : ℝ) * HLm Γ 5 L839 + (-1 : ℝ) * HLm Γ 5 L842 + (-1 : ℝ) * HLm Γ 5 L3226 := by
  have h := HLm_submod hΓ [F1] L3227 [F7]
  rw [show [F1] ++ L3227 ++ [F7] = L4240 from rfl, show [F1] ++ L3227 = L4238 from rfl,
    show L3227 ++ [F7] = L4239 from rfl] at h
  rw [i2371 hinj, i2369 hinj, i2370 hinj, i1823 hinj] at h
  linarith

theorem row902 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4241 + (1 : ℝ) * HLm Γ 5 L4243 + (-1 : ℝ) * HLm Γ 5 L4245 + (-1 : ℝ) * HLm Γ 5 L986 := by
  have h := HLm_submod hΓ [F210] L987 [F33]
  rw [show [F210] ++ L987 ++ [F33] = L4246 from rfl, show [F210] ++ L987 = L4242 from rfl,
    show L987 ++ [F33] = L4244 from rfl] at h
  rw [i2374 hinj, i2372 hinj, i2373 hinj, i458 hinj] at h
  linarith

theorem row903 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2241 + (1 : ℝ) * HLm Γ 5 L1001 + (-1 : ℝ) * HLm Γ 5 L2670 + (-1 : ℝ) * HLm Γ 5 L295 := by
  have h := HLm_submod hΓ [F7] L295 [F3]
  rw [show [F7] ++ L295 ++ [F3] = L4248 from rfl, show [F7] ++ L295 = L4247 from rfl,
    show L295 ++ [F3] = L1002 from rfl] at h
  rw [i2376 hinj, i2375 hinj, i466 hinj] at h
  linarith

theorem row904 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1278 + (1 : ℝ) * HLm Γ 5 L4250 + (-1 : ℝ) * HLm Γ 5 L4252 + (-1 : ℝ) * HLm Γ 5 L4254 := by
  have h := HLm_submod hΓ [F4] L4255 [F210]
  rw [show [F4] ++ L4255 ++ [F210] = L4253 from rfl, show [F4] ++ L4255 = L4249 from rfl,
    show L4255 ++ [F210] = L4251 from rfl] at h
  rw [i2379 hinj, i2377 hinj, i2378 hinj, i2380 hinj] at h
  linarith

theorem row905 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1458 + (1 : ℝ) * HLm Γ 5 L3259 + (-1 : ℝ) * HLm Γ 5 L4258 + (-1 : ℝ) * HLm Γ 5 L2210 := by
  have h := HLm_submod hΓ [F7] L4260 [F210]
  rw [show [F7] ++ L4260 ++ [F210] = L4259 from rfl, show [F7] ++ L4260 = L4256 from rfl,
    show L4260 ++ [F210] = L4257 from rfl] at h
  rw [i2383 hinj, i2381 hinj, i2382 hinj, i2384 hinj] at h
  linarith

theorem row906 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4261 + (1 : ℝ) * HLm Γ 5 L4263 + (-1 : ℝ) * HLm Γ 5 L4265 + (-1 : ℝ) * HLm Γ 5 L3247 := by
  have h := HLm_submod hΓ [F210] L4267 [F25]
  rw [show [F210] ++ L4267 ++ [F25] = L4266 from rfl, show [F210] ++ L4267 = L4262 from rfl,
    show L4267 ++ [F25] = L4264 from rfl] at h
  rw [i2387 hinj, i2385 hinj, i2386 hinj, i2388 hinj] at h
  linarith

theorem row907 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3243 + (1 : ℝ) * HLm Γ 5 L4268 + (-1 : ℝ) * HLm Γ 5 L4270 + (-1 : ℝ) * HLm Γ 5 L3241 := by
  have h := HLm_submod hΓ [F228] L3242 [F86]
  rw [show [F228] ++ L3242 ++ [F86] = L4271 from rfl, show [F228] ++ L3242 = L3244 from rfl,
    show L3242 ++ [F86] = L4269 from rfl] at h
  rw [i2390 hinj, i1831 hinj, i2389 hinj, i1830 hinj] at h
  linarith

theorem row908 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1458 + (1 : ℝ) * HLm Γ 5 L3265 + (-1 : ℝ) * HLm Γ 5 L4274 + (-1 : ℝ) * HLm Γ 5 L3261 := by
  have h := HLm_submod hΓ [F7] L4276 [F214]
  rw [show [F7] ++ L4276 ++ [F214] = L4275 from rfl, show [F7] ++ L4276 = L4272 from rfl,
    show L4276 ++ [F214] = L4273 from rfl] at h
  rw [i2393 hinj, i2391 hinj, i2392 hinj, i2394 hinj] at h
  linarith

theorem row909 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4277 + (1 : ℝ) * HLm Γ 5 L4279 + (-1 : ℝ) * HLm Γ 5 L4281 + (-1 : ℝ) * HLm Γ 5 L4283 := by
  have h := HLm_submod hΓ [F2] L4284 [F228]
  rw [show [F2] ++ L4284 ++ [F228] = L4282 from rfl, show [F2] ++ L4284 = L4278 from rfl,
    show L4284 ++ [F228] = L4280 from rfl] at h
  rw [i2397 hinj, i2395 hinj, i2396 hinj, i2398 hinj] at h
  linarith

theorem row910 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4285 + (1 : ℝ) * HLm Γ 5 L4287 + (-1 : ℝ) * HLm Γ 5 L4289 + (-1 : ℝ) * HLm Γ 5 L4291 := by
  have h := HLm_submod hΓ [F44] L4292 [F210]
  rw [show [F44] ++ L4292 ++ [F210] = L4290 from rfl, show [F44] ++ L4292 = L4286 from rfl,
    show L4292 ++ [F210] = L4288 from rfl] at h
  rw [i2401 hinj, i2399 hinj, i2400 hinj, i2402 hinj] at h
  linarith

theorem row911 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3012 + (1 : ℝ) * HLm Γ 5 L3228 + (-1 : ℝ) * HLm Γ 5 L4295 + (-1 : ℝ) * HLm Γ 5 L4065 := by
  have h := HLm_submod hΓ [F7] L4065 [F3]
  rw [show [F7] ++ L4065 ++ [F3] = L4296 from rfl, show [F7] ++ L4065 = L4293 from rfl,
    show L4065 ++ [F3] = L4294 from rfl] at h
  rw [i2405 hinj, i2403 hinj, i2404 hinj] at h
  linarith

theorem row912 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3012 + (1 : ℝ) * HLm Γ 5 L3254 + (-1 : ℝ) * HLm Γ 5 L4298 + (-1 : ℝ) * HLm Γ 5 L4065 := by
  have h := HLm_submod hΓ [F7] L4065 [F33]
  rw [show [F7] ++ L4065 ++ [F33] = L4299 from rfl, show [F7] ++ L4065 = L4293 from rfl,
    show L4065 ++ [F33] = L4297 from rfl] at h
  rw [i2407 hinj, i2403 hinj, i2406 hinj] at h
  linarith

theorem row913 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L788 + (1 : ℝ) * HLm Γ 5 L1835 + (-1 : ℝ) * HLm Γ 5 L1832 + (-1 : ℝ) * HLm Γ 5 L4303 := by
  have h := HLm_submod hΓ [F7] L4304 [F6]
  rw [show [F7] ++ L4304 ++ [F6] = L4302 from rfl, show [F7] ++ L4304 = L4300 from rfl,
    show L4304 ++ [F6] = L4301 from rfl] at h
  rw [i2410 hinj, i2408 hinj, i2409 hinj, i2411 hinj] at h
  linarith

theorem row914 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L683 + (1 : ℝ) * HLm Γ 5 L2575 + (-1 : ℝ) * HLm Γ 5 L842 + (-1 : ℝ) * HLm Γ 5 L3298 := by
  have h := HLm_submod hΓ [F0] L4308 [F2]
  rw [show [F0] ++ L4308 ++ [F2] = L4307 from rfl, show [F0] ++ L4308 = L4305 from rfl,
    show L4308 ++ [F2] = L4306 from rfl] at h
  rw [i2414 hinj, i2412 hinj, i2413 hinj, i2415 hinj] at h
  linarith

theorem row915 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4309 + (1 : ℝ) * HLm Γ 5 L4311 + (-1 : ℝ) * HLm Γ 5 L4313 + (-1 : ℝ) * HLm Γ 5 L3298 := by
  have h := HLm_submod hΓ [F12] L4308 [F210]
  rw [show [F12] ++ L4308 ++ [F210] = L4314 from rfl, show [F12] ++ L4308 = L4310 from rfl,
    show L4308 ++ [F210] = L4312 from rfl] at h
  rw [i2418 hinj, i2416 hinj, i2417 hinj, i2415 hinj] at h
  linarith

theorem row916 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3679 + (1 : ℝ) * HLm Γ 5 L3307 + (-1 : ℝ) * HLm Γ 5 L4317 + (-1 : ℝ) * HLm Γ 5 L3304 := by
  have h := HLm_submod hΓ [F0] L4319 [F16]
  rw [show [F0] ++ L4319 ++ [F16] = L4318 from rfl, show [F0] ++ L4319 = L4315 from rfl,
    show L4319 ++ [F16] = L4316 from rfl] at h
  rw [i2421 hinj, i2419 hinj, i2420 hinj, i2422 hinj] at h
  linarith

theorem row917 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4320 + (1 : ℝ) * HLm Γ 5 L4322 + (-1 : ℝ) * HLm Γ 5 L4324 + (-1 : ℝ) * HLm Γ 5 L3287 := by
  have h := HLm_submod hΓ [F111] L3288 [F210]
  rw [show [F111] ++ L3288 ++ [F210] = L4325 from rfl, show [F111] ++ L3288 = L4321 from rfl,
    show L3288 ++ [F210] = L4323 from rfl] at h
  rw [i2425 hinj, i2423 hinj, i2424 hinj, i1853 hinj] at h
  linarith

theorem row918 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L731 + (1 : ℝ) * HLm Γ 5 L4327 + (-1 : ℝ) * HLm Γ 5 L4329 + (-1 : ℝ) * HLm Γ 5 L1079 := by
  have h := HLm_submod hΓ [F0] L4331 [F210]
  rw [show [F0] ++ L4331 ++ [F210] = L4330 from rfl, show [F0] ++ L4331 = L4326 from rfl,
    show L4331 ++ [F210] = L4328 from rfl] at h
  rw [i2428 hinj, i2426 hinj, i2427 hinj, i2429 hinj] at h
  linarith

theorem row919 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4332 + (1 : ℝ) * HLm Γ 5 L4334 + (-1 : ℝ) * HLm Γ 5 L4336 + (-1 : ℝ) * HLm Γ 5 L3292 := by
  have h := HLm_submod hΓ [F46] L4338 [F210]
  rw [show [F46] ++ L4338 ++ [F210] = L4337 from rfl, show [F46] ++ L4338 = L4333 from rfl,
    show L4338 ++ [F210] = L4335 from rfl] at h
  rw [i2432 hinj, i2430 hinj, i2431 hinj, i2433 hinj] at h
  linarith

theorem row920 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4339 + (1 : ℝ) * HLm Γ 5 L4341 + (-1 : ℝ) * HLm Γ 5 L4343 + (-1 : ℝ) * HLm Γ 5 L4345 := by
  have h := HLm_submod hΓ [F12] L4346 [F210]
  rw [show [F12] ++ L4346 ++ [F210] = L4344 from rfl, show [F12] ++ L4346 = L4340 from rfl,
    show L4346 ++ [F210] = L4342 from rfl] at h
  rw [i2436 hinj, i2434 hinj, i2435 hinj, i2437 hinj] at h
  linarith

theorem row921 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3439 + (1 : ℝ) * HLm Γ 5 L4348 + (-1 : ℝ) * HLm Γ 5 L4350 + (-1 : ℝ) * HLm Γ 5 L4352 := by
  have h := HLm_submod hΓ [F2] L4353 [F228]
  rw [show [F2] ++ L4353 ++ [F228] = L4351 from rfl, show [F2] ++ L4353 = L4347 from rfl,
    show L4353 ++ [F228] = L4349 from rfl] at h
  rw [i2440 hinj, i2438 hinj, i2439 hinj, i2441 hinj] at h
  linarith

theorem row922 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4354 + (1 : ℝ) * HLm Γ 5 L4356 + (-1 : ℝ) * HLm Γ 5 L4358 + (-1 : ℝ) * HLm Γ 5 L4360 := by
  have h := HLm_submod hΓ [F2] L4361 [F27]
  rw [show [F2] ++ L4361 ++ [F27] = L4359 from rfl, show [F2] ++ L4361 = L4355 from rfl,
    show L4361 ++ [F27] = L4357 from rfl] at h
  rw [i2444 hinj, i2442 hinj, i2443 hinj, i2445 hinj] at h
  linarith

theorem row923 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4362 + (1 : ℝ) * HLm Γ 5 L4364 + (-1 : ℝ) * HLm Γ 5 L4366 + (-1 : ℝ) * HLm Γ 5 L3299 := by
  have h := HLm_submod hΓ [F2] L3300 [F0]
  rw [show [F2] ++ L3300 ++ [F0] = L4367 from rfl, show [F2] ++ L3300 = L4363 from rfl,
    show L3300 ++ [F0] = L4365 from rfl] at h
  rw [i2448 hinj, i2446 hinj, i2447 hinj, i1860 hinj] at h
  linarith

theorem row924 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4368 + (1 : ℝ) * HLm Γ 5 L4370 + (-1 : ℝ) * HLm Γ 5 L4372 + (-1 : ℝ) * HLm Γ 5 L4374 := by
  have h := HLm_submod hΓ [F210] L4375 [F33]
  rw [show [F210] ++ L4375 ++ [F33] = L4373 from rfl, show [F210] ++ L4375 = L4369 from rfl,
    show L4375 ++ [F33] = L4371 from rfl] at h
  rw [i2451 hinj, i2449 hinj, i2450 hinj, i2452 hinj] at h
  linarith

theorem row925 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4059 + (1 : ℝ) * HLm Γ 5 L4377 + (-1 : ℝ) * HLm Γ 5 L4379 + (-1 : ℝ) * HLm Γ 5 L4381 := by
  have h := HLm_submod hΓ [F210] L4382 [F85]
  rw [show [F210] ++ L4382 ++ [F85] = L4380 from rfl, show [F210] ++ L4382 = L4376 from rfl,
    show L4382 ++ [F85] = L4378 from rfl] at h
  rw [i2455 hinj, i2453 hinj, i2454 hinj, i2456 hinj] at h
  linarith

theorem row926 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L851 + (1 : ℝ) * HLm Γ 5 L3319 + (-1 : ℝ) * HLm Γ 5 L3517 + (-1 : ℝ) * HLm Γ 5 L624 := by
  have h := HLm_submod hΓ [F0] L1375 [F217]
  rw [show [F0] ++ L1375 ++ [F217] = L4384 from rfl, show [F0] ++ L1375 = L1371 from rfl,
    show L1375 ++ [F217] = L4383 from rfl] at h
  rw [i2458 hinj, i683 hinj, i2457 hinj, i686 hinj] at h
  linarith

theorem row927 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4385 + (1 : ℝ) * HLm Γ 5 L4387 + (-1 : ℝ) * HLm Γ 5 L4389 + (-1 : ℝ) * HLm Γ 5 L4149 := by
  have h := HLm_submod hΓ [F52] L4391 [F214]
  rw [show [F52] ++ L4391 ++ [F214] = L4390 from rfl, show [F52] ++ L4391 = L4386 from rfl,
    show L4391 ++ [F214] = L4388 from rfl] at h
  rw [i2461 hinj, i2459 hinj, i2460 hinj, i2462 hinj] at h
  linarith

theorem row928 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4392 + (1 : ℝ) * HLm Γ 5 L3457 + (-1 : ℝ) * HLm Γ 5 L4394 + (-1 : ℝ) * HLm Γ 5 L1401 := by
  have h := HLm_submod hΓ [F210] L1402 [F6]
  rw [show [F210] ++ L1402 ++ [F6] = L4395 from rfl, show [F210] ++ L1402 = L4393 from rfl,
    show L1402 ++ [F6] = L3458 from rfl] at h
  rw [i2464 hinj, i2463 hinj, i1940 hinj, i702 hinj] at h
  linarith

theorem row929 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4396 + (1 : ℝ) * HLm Γ 5 L4398 + (-1 : ℝ) * HLm Γ 5 L4400 + (-1 : ℝ) * HLm Γ 5 L3379 := by
  have h := HLm_submod hΓ [F47] L4402 [F219]
  rw [show [F47] ++ L4402 ++ [F219] = L4401 from rfl, show [F47] ++ L4402 = L4397 from rfl,
    show L4402 ++ [F219] = L4399 from rfl] at h
  rw [i2467 hinj, i2465 hinj, i2466 hinj, i2468 hinj] at h
  linarith

theorem row930 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3635 + (1 : ℝ) * HLm Γ 5 L4404 + (-1 : ℝ) * HLm Γ 5 L4406 + (-1 : ℝ) * HLm Γ 5 L3312 := by
  have h := HLm_submod hΓ [F1] L3313 [F16]
  rw [show [F1] ++ L3313 ++ [F16] = L4407 from rfl, show [F1] ++ L3313 = L4403 from rfl,
    show L3313 ++ [F16] = L4405 from rfl] at h
  rw [i2471 hinj, i2469 hinj, i2470 hinj, i1866 hinj] at h
  linarith

theorem row931 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4408 + (1 : ℝ) * HLm Γ 5 L3660 + (-1 : ℝ) * HLm Γ 5 L4410 + (-1 : ℝ) * HLm Γ 5 L3658 := by
  have h := HLm_submod hΓ [F1] L3659 [F67]
  rw [show [F1] ++ L3659 ++ [F67] = L4411 from rfl, show [F1] ++ L3659 = L4409 from rfl,
    show L3659 ++ [F67] = L3661 from rfl] at h
  rw [i2473 hinj, i2472 hinj, i2049 hinj, i2048 hinj] at h
  linarith

theorem row932 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4412 + (1 : ℝ) * HLm Γ 5 L3401 + (-1 : ℝ) * HLm Γ 5 L4295 + (-1 : ℝ) * HLm Γ 5 L4416 := by
  have h := HLm_submod hΓ [F0] L4417 [F6]
  rw [show [F0] ++ L4417 ++ [F6] = L4415 from rfl, show [F0] ++ L4417 = L4413 from rfl,
    show L4417 ++ [F6] = L4414 from rfl] at h
  rw [i2476 hinj, i2474 hinj, i2475 hinj, i2477 hinj] at h
  linarith

theorem row933 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4418 + (1 : ℝ) * HLm Γ 5 L1874 + (-1 : ℝ) * HLm Γ 5 L4420 + (-1 : ℝ) * HLm Γ 5 L3323 := by
  have h := HLm_submod hΓ [F211] L3323 [F36]
  rw [show [F211] ++ L3323 ++ [F36] = L4421 from rfl, show [F211] ++ L3323 = L4418 from rfl,
    show L3323 ++ [F36] = L4419 from rfl] at h
  rw [i2479 hinj, i2478 hinj] at h
  linarith

theorem row934 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3314 + (1 : ℝ) * HLm Γ 5 L4423 + (-1 : ℝ) * HLm Γ 5 L4425 + (-1 : ℝ) * HLm Γ 5 L3318 := by
  have h := HLm_submod hΓ [F47] L3318 [F16]
  rw [show [F47] ++ L3318 ++ [F16] = L4426 from rfl, show [F47] ++ L3318 = L4422 from rfl,
    show L3318 ++ [F16] = L4424 from rfl] at h
  rw [i2482 hinj, i2480 hinj, i2481 hinj] at h
  linarith

theorem row935 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2241 + (1 : ℝ) * HLm Γ 5 L4427 + (-1 : ℝ) * HLm Γ 5 L4429 + (-1 : ℝ) * HLm Γ 5 L305 := by
  have h := HLm_submod hΓ [F0] L2050 [F214]
  rw [show [F0] ++ L2050 ++ [F214] = L4430 from rfl, show [F0] ++ L2050 = L2242 from rfl,
    show L2050 ++ [F214] = L4428 from rfl] at h
  rw [i2484 hinj, i1232 hinj, i2483 hinj, i1124 hinj] at h
  linarith

theorem row936 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4431 + (1 : ℝ) * HLm Γ 5 L4433 + (-1 : ℝ) * HLm Γ 5 L4435 + (-1 : ℝ) * HLm Γ 5 L4437 := by
  have h := HLm_submod hΓ [F2] L4438 [F210]
  rw [show [F2] ++ L4438 ++ [F210] = L4436 from rfl, show [F2] ++ L4438 = L4432 from rfl,
    show L4438 ++ [F210] = L4434 from rfl] at h
  rw [i2487 hinj, i2485 hinj, i2486 hinj, i2488 hinj] at h
  linarith

theorem row937 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2338 + (1 : ℝ) * HLm Γ 5 L3804 + (-1 : ℝ) * HLm Γ 5 L4441 + (-1 : ℝ) * HLm Γ 5 L4443 := by
  have h := HLm_submod hΓ [F0] L4444 [F236]
  rw [show [F0] ++ L4444 ++ [F236] = L4442 from rfl, show [F0] ++ L4444 = L4439 from rfl,
    show L4444 ++ [F236] = L4440 from rfl] at h
  rw [i2491 hinj, i2489 hinj, i2490 hinj, i2492 hinj] at h
  linarith

theorem row938 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4174 + (1 : ℝ) * HLm Γ 5 L4446 + (-1 : ℝ) * HLm Γ 5 L4448 + (-1 : ℝ) * HLm Γ 5 L4450 := by
  have h := HLm_submod hΓ [F12] L4451 [F67]
  rw [show [F12] ++ L4451 ++ [F67] = L4449 from rfl, show [F12] ++ L4451 = L4445 from rfl,
    show L4451 ++ [F67] = L4447 from rfl] at h
  rw [i2495 hinj, i2493 hinj, i2494 hinj, i2496 hinj] at h
  linarith

theorem row939 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4452 + (1 : ℝ) * HLm Γ 5 L3375 + (-1 : ℝ) * HLm Γ 5 L4455 + (-1 : ℝ) * HLm Γ 5 L3371 := by
  have h := HLm_submod hΓ [F0] L4457 [F236]
  rw [show [F0] ++ L4457 ++ [F236] = L4456 from rfl, show [F0] ++ L4457 = L4453 from rfl,
    show L4457 ++ [F236] = L4454 from rfl] at h
  rw [i2499 hinj, i2497 hinj, i2498 hinj, i2500 hinj] at h
  linarith

theorem row940 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1171 + (1 : ℝ) * HLm Γ 5 L4459 + (-1 : ℝ) * HLm Γ 5 L4461 + (-1 : ℝ) * HLm Γ 5 L4463 := by
  have h := HLm_submod hΓ [F1] L4464 [F219]
  rw [show [F1] ++ L4464 ++ [F219] = L4462 from rfl, show [F1] ++ L4464 = L4458 from rfl,
    show L4464 ++ [F219] = L4460 from rfl] at h
  rw [i2503 hinj, i2501 hinj, i2502 hinj, i2504 hinj] at h
  linarith

theorem row941 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4465 + (1 : ℝ) * HLm Γ 5 L4467 + (-1 : ℝ) * HLm Γ 5 L4469 + (-1 : ℝ) * HLm Γ 5 L4471 := by
  have h := HLm_submod hΓ [F210] L4472 [F36]
  rw [show [F210] ++ L4472 ++ [F36] = L4470 from rfl, show [F210] ++ L4472 = L4466 from rfl,
    show L4472 ++ [F36] = L4468 from rfl] at h
  rw [i2507 hinj, i2505 hinj, i2506 hinj, i2508 hinj] at h
  linarith

theorem row942 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3364 + (1 : ℝ) * HLm Γ 5 L4473 + (-1 : ℝ) * HLm Γ 5 L4475 + (-1 : ℝ) * HLm Γ 5 L3362 := by
  have h := HLm_submod hΓ [F211] L3363 [F45]
  rw [show [F211] ++ L3363 ++ [F45] = L4476 from rfl, show [F211] ++ L3363 = L3365 from rfl,
    show L3363 ++ [F45] = L4474 from rfl] at h
  rw [i2510 hinj, i1891 hinj, i2509 hinj, i1890 hinj] at h
  linarith

theorem row943 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4477 + (1 : ℝ) * HLm Γ 5 L4479 + (-1 : ℝ) * HLm Γ 5 L4481 + (-1 : ℝ) * HLm Γ 5 L4483 := by
  have h := HLm_submod hΓ [F3] L4484 [F211]
  rw [show [F3] ++ L4484 ++ [F211] = L4482 from rfl, show [F3] ++ L4484 = L4478 from rfl,
    show L4484 ++ [F211] = L4480 from rfl] at h
  rw [i2513 hinj, i2511 hinj, i2512 hinj, i2514 hinj] at h
  linarith

theorem row944 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4485 + (1 : ℝ) * HLm Γ 5 L4486 + (-1 : ℝ) * HLm Γ 5 L4488 + (-1 : ℝ) * HLm Γ 5 L4490 := by
  have h := HLm_submod hΓ [F211] L4490 [F36]
  rw [show [F211] ++ L4490 ++ [F36] = L4489 from rfl, show [F211] ++ L4490 = L4485 from rfl,
    show L4490 ++ [F36] = L4487 from rfl] at h
  rw [i2516 hinj, i2515 hinj] at h
  linarith

theorem row945 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4491 + (1 : ℝ) * HLm Γ 5 L4493 + (-1 : ℝ) * HLm Γ 5 L4495 + (-1 : ℝ) * HLm Γ 5 L4497 := by
  have h := HLm_submod hΓ [F211] L4498 [F55]
  rw [show [F211] ++ L4498 ++ [F55] = L4496 from rfl, show [F211] ++ L4498 = L4492 from rfl,
    show L4498 ++ [F55] = L4494 from rfl] at h
  rw [i2519 hinj, i2517 hinj, i2518 hinj, i2520 hinj] at h
  linarith

theorem row946 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4499 + (1 : ℝ) * HLm Γ 5 L4501 + (-1 : ℝ) * HLm Γ 5 L4503 + (-1 : ℝ) * HLm Γ 5 L4505 := by
  have h := HLm_submod hΓ [F0] L4506 [F34]
  rw [show [F0] ++ L4506 ++ [F34] = L4504 from rfl, show [F0] ++ L4506 = L4500 from rfl,
    show L4506 ++ [F34] = L4502 from rfl] at h
  rw [i2523 hinj, i2521 hinj, i2522 hinj, i2524 hinj] at h
  linarith

theorem row947 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4507 + (1 : ℝ) * HLm Γ 5 L4509 + (-1 : ℝ) * HLm Γ 5 L4511 + (-1 : ℝ) * HLm Γ 5 L4513 := by
  have h := HLm_submod hΓ [F0] L4514 [F36]
  rw [show [F0] ++ L4514 ++ [F36] = L4512 from rfl, show [F0] ++ L4514 = L4508 from rfl,
    show L4514 ++ [F36] = L4510 from rfl] at h
  rw [i2527 hinj, i2525 hinj, i2526 hinj, i2528 hinj] at h
  linarith

theorem row948 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3012 + (1 : ℝ) * HLm Γ 5 L4516 + (-1 : ℝ) * HLm Γ 5 L4298 + (-1 : ℝ) * HLm Γ 5 L3399 := by
  have h := HLm_submod hΓ [F0] L4519 [F34]
  rw [show [F0] ++ L4519 ++ [F34] = L4518 from rfl, show [F0] ++ L4519 = L4515 from rfl,
    show L4519 ++ [F34] = L4517 from rfl] at h
  rw [i2531 hinj, i2529 hinj, i2530 hinj, i2532 hinj] at h
  linarith

theorem row949 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3279 + (1 : ℝ) * HLm Γ 5 L4520 + (-1 : ℝ) * HLm Γ 5 L4522 + (-1 : ℝ) * HLm Γ 5 L3367 := by
  have h := HLm_submod hΓ [F0] L3368 [F34]
  rw [show [F0] ++ L3368 ++ [F34] = L4523 from rfl, show [F0] ++ L3368 = L3369 from rfl,
    show L3368 ++ [F34] = L4521 from rfl] at h
  rw [i2534 hinj, i1893 hinj, i2533 hinj, i1892 hinj] at h
  linarith

theorem row950 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3392 + (1 : ℝ) * HLm Γ 5 L4525 + (-1 : ℝ) * HLm Γ 5 L4527 + (-1 : ℝ) * HLm Γ 5 L3390 := by
  have h := HLm_submod hΓ [F210] L4529 [F85]
  rw [show [F210] ++ L4529 ++ [F85] = L4528 from rfl, show [F210] ++ L4529 = L4524 from rfl,
    show L4529 ++ [F85] = L4526 from rfl] at h
  rw [i2537 hinj, i2535 hinj, i2536 hinj, i2538 hinj] at h
  linarith

theorem row951 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4530 + (1 : ℝ) * HLm Γ 5 L1150 + (-1 : ℝ) * HLm Γ 5 L4533 + (-1 : ℝ) * HLm Γ 5 L1143 := by
  have h := HLm_submod hΓ [F210] L4535 [F55]
  rw [show [F210] ++ L4535 ++ [F55] = L4534 from rfl, show [F210] ++ L4535 = L4531 from rfl,
    show L4535 ++ [F55] = L4532 from rfl] at h
  rw [i2541 hinj, i2539 hinj, i2540 hinj, i2542 hinj] at h
  linarith

theorem row952 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4536 + (1 : ℝ) * HLm Γ 5 L4538 + (-1 : ℝ) * HLm Γ 5 L4540 + (-1 : ℝ) * HLm Γ 5 L662 := by
  have h := HLm_submod hΓ [F211] L4542 [F6]
  rw [show [F211] ++ L4542 ++ [F6] = L4541 from rfl, show [F211] ++ L4542 = L4537 from rfl,
    show L4542 ++ [F6] = L4539 from rfl] at h
  rw [i2545 hinj, i2543 hinj, i2544 hinj, i2546 hinj] at h
  linarith

theorem row953 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3405 + (1 : ℝ) * HLm Γ 5 L4544 + (-1 : ℝ) * HLm Γ 5 L4546 + (-1 : ℝ) * HLm Γ 5 L3403 := by
  have h := HLm_submod hΓ [F0] L4548 [F55]
  rw [show [F0] ++ L4548 ++ [F55] = L4547 from rfl, show [F0] ++ L4548 = L4543 from rfl,
    show L4548 ++ [F55] = L4545 from rfl] at h
  rw [i2549 hinj, i2547 hinj, i2548 hinj, i2550 hinj] at h
  linarith

theorem row954 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1664 + (1 : ℝ) * HLm Γ 5 L4550 + (-1 : ℝ) * HLm Γ 5 L4552 + (-1 : ℝ) * HLm Γ 5 L2139 := by
  have h := HLm_submod hΓ [F12] L2140 [F211]
  rw [show [F12] ++ L2140 ++ [F211] = L4553 from rfl, show [F12] ++ L2140 = L4549 from rfl,
    show L2140 ++ [F211] = L4551 from rfl] at h
  rw [i2553 hinj, i2551 hinj, i2552 hinj, i1173 hinj] at h
  linarith

theorem row955 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4554 + (1 : ℝ) * HLm Γ 5 L4556 + (-1 : ℝ) * HLm Γ 5 L4558 + (-1 : ℝ) * HLm Γ 5 L4170 := by
  have h := HLm_submod hΓ [F0] L4171 [F36]
  rw [show [F0] ++ L4171 ++ [F36] = L4559 from rfl, show [F0] ++ L4171 = L4555 from rfl,
    show L4171 ++ [F36] = L4557 from rfl] at h
  rw [i2556 hinj, i2554 hinj, i2555 hinj, i2329 hinj] at h
  linarith

theorem row956 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3409 + (1 : ℝ) * HLm Γ 5 L4183 + (-1 : ℝ) * HLm Γ 5 L4562 + (-1 : ℝ) * HLm Γ 5 L3407 := by
  have h := HLm_submod hΓ [F0] L4564 [F43]
  rw [show [F0] ++ L4564 ++ [F43] = L4563 from rfl, show [F0] ++ L4564 = L4560 from rfl,
    show L4564 ++ [F43] = L4561 from rfl] at h
  rw [i2559 hinj, i2557 hinj, i2558 hinj, i2560 hinj] at h
  linarith

theorem row957 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3396 + (1 : ℝ) * HLm Γ 5 L3301 + (-1 : ℝ) * HLm Γ 5 L4566 + (-1 : ℝ) * HLm Γ 5 L3394 := by
  have h := HLm_submod hΓ [F0] L3395 [F1]
  rw [show [F0] ++ L3395 ++ [F1] = L4567 from rfl, show [F0] ++ L3395 = L3397 from rfl,
    show L3395 ++ [F1] = L4565 from rfl] at h
  rw [i2562 hinj, i1907 hinj, i2561 hinj, i1906 hinj] at h
  linarith

theorem row958 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L715 + (1 : ℝ) * HLm Γ 5 L4569 + (-1 : ℝ) * HLm Γ 5 L4571 + (-1 : ℝ) * HLm Γ 5 L712 := by
  have h := HLm_submod hΓ [F67] L713 [F17]
  rw [show [F67] ++ L713 ++ [F17] = L4572 from rfl, show [F67] ++ L713 = L4568 from rfl,
    show L713 ++ [F17] = L4570 from rfl] at h
  rw [i2565 hinj, i2563 hinj, i2564 hinj, i312 hinj] at h
  linarith

theorem row959 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3415 + (1 : ℝ) * HLm Γ 5 L4573 + (-1 : ℝ) * HLm Γ 5 L4575 + (-1 : ℝ) * HLm Γ 5 L3413 := by
  have h := HLm_submod hΓ [F16] L3414 [F52]
  rw [show [F16] ++ L3414 ++ [F52] = L4576 from rfl, show [F16] ++ L3414 = L3416 from rfl,
    show L3414 ++ [F52] = L4574 from rfl] at h
  rw [i2567 hinj, i1917 hinj, i2566 hinj, i1916 hinj] at h
  linarith

theorem row960 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4214 + (1 : ℝ) * HLm Γ 5 L3600 + (-1 : ℝ) * HLm Γ 5 L4579 + (-1 : ℝ) * HLm Γ 5 L4581 := by
  have h := HLm_submod hΓ [F0] L4582 [F43]
  rw [show [F0] ++ L4582 ++ [F43] = L4580 from rfl, show [F0] ++ L4582 = L4577 from rfl,
    show L4582 ++ [F43] = L4578 from rfl] at h
  rw [i2570 hinj, i2568 hinj, i2569 hinj, i2571 hinj] at h
  linarith

theorem row961 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4043 + (1 : ℝ) * HLm Γ 5 L4584 + (-1 : ℝ) * HLm Γ 5 L4586 + (-1 : ℝ) * HLm Γ 5 L3596 := by
  have h := HLm_submod hΓ [F211] L3597 [F55]
  rw [show [F211] ++ L3597 ++ [F55] = L4587 from rfl, show [F211] ++ L3597 = L4583 from rfl,
    show L3597 ++ [F55] = L4585 from rfl] at h
  rw [i2574 hinj, i2572 hinj, i2573 hinj, i2015 hinj] at h
  linarith

theorem row962 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1465 + (1 : ℝ) * HLm Γ 5 L4589 + (-1 : ℝ) * HLm Γ 5 L904 + (-1 : ℝ) * HLm Γ 5 L4592 := by
  have h := HLm_submod hΓ [F1] L4593 [F7]
  rw [show [F1] ++ L4593 ++ [F7] = L4591 from rfl, show [F1] ++ L4593 = L4588 from rfl,
    show L4593 ++ [F7] = L4590 from rfl] at h
  rw [i2577 hinj, i2575 hinj, i2576 hinj, i2578 hinj] at h
  linarith

theorem row963 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1465 + (1 : ℝ) * HLm Γ 5 L4594 + (-1 : ℝ) * HLm Γ 5 L4596 + (-1 : ℝ) * HLm Γ 5 L4592 := by
  have h := HLm_submod hΓ [F1] L4593 [F85]
  rw [show [F1] ++ L4593 ++ [F85] = L4597 from rfl, show [F1] ++ L4593 = L4588 from rfl,
    show L4593 ++ [F85] = L4595 from rfl] at h
  rw [i2580 hinj, i2575 hinj, i2579 hinj, i2578 hinj] at h
  linarith

theorem row964 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4354 + (1 : ℝ) * HLm Γ 5 L4599 + (-1 : ℝ) * HLm Γ 5 L4358 + (-1 : ℝ) * HLm Γ 5 L4602 := by
  have h := HLm_submod hΓ [F1] L4603 [F27]
  rw [show [F1] ++ L4603 ++ [F27] = L4601 from rfl, show [F1] ++ L4603 = L4598 from rfl,
    show L4603 ++ [F27] = L4600 from rfl] at h
  rw [i2583 hinj, i2581 hinj, i2582 hinj, i2584 hinj] at h
  linarith

theorem row965 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4604 + (1 : ℝ) * HLm Γ 5 L4606 + (-1 : ℝ) * HLm Γ 5 L4586 + (-1 : ℝ) * HLm Γ 5 L4609 := by
  have h := HLm_submod hΓ [F9] L4610 [F43]
  rw [show [F9] ++ L4610 ++ [F43] = L4608 from rfl, show [F9] ++ L4610 = L4605 from rfl,
    show L4610 ++ [F43] = L4607 from rfl] at h
  rw [i2587 hinj, i2585 hinj, i2586 hinj, i2588 hinj] at h
  linarith

theorem row966 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3423 + (1 : ℝ) * HLm Γ 5 L4611 + (-1 : ℝ) * HLm Γ 5 L4613 + (-1 : ℝ) * HLm Γ 5 L3421 := by
  have h := HLm_submod hΓ [F9] L3422 [F55]
  rw [show [F9] ++ L3422 ++ [F55] = L4614 from rfl, show [F9] ++ L3422 = L3424 from rfl,
    show L3422 ++ [F55] = L4612 from rfl] at h
  rw [i2590 hinj, i1921 hinj, i2589 hinj, i1920 hinj] at h
  linarith

theorem row967 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3600 + (1 : ℝ) * HLm Γ 5 L4616 + (-1 : ℝ) * HLm Γ 5 L4618 + (-1 : ℝ) * HLm Γ 5 L4058 := by
  have h := HLm_submod hΓ [F9] L4062 [F16]
  rw [show [F9] ++ L4062 ++ [F16] = L4619 from rfl, show [F9] ++ L4062 = L4615 from rfl,
    show L4062 ++ [F16] = L4617 from rfl] at h
  rw [i2593 hinj, i2591 hinj, i2592 hinj, i2266 hinj] at h
  linarith

theorem row968 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4620 + (1 : ℝ) * HLm Γ 5 L4622 + (-1 : ℝ) * HLm Γ 5 L4624 + (-1 : ℝ) * HLm Γ 5 L3434 := by
  have h := HLm_submod hΓ [F1] L3435 [F68]
  rw [show [F1] ++ L3435 ++ [F68] = L4625 from rfl, show [F1] ++ L3435 = L4621 from rfl,
    show L3435 ++ [F68] = L4623 from rfl] at h
  rw [i2596 hinj, i2594 hinj, i2595 hinj, i1927 hinj] at h
  linarith

theorem row969 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4626 + (1 : ℝ) * HLm Γ 5 L4628 + (-1 : ℝ) * HLm Γ 5 L4630 + (-1 : ℝ) * HLm Γ 5 L4104 := by
  have h := HLm_submod hΓ [F1] L4105 [F52]
  rw [show [F1] ++ L4105 ++ [F52] = L4631 from rfl, show [F1] ++ L4105 = L4627 from rfl,
    show L4105 ++ [F52] = L4629 from rfl] at h
  rw [i2599 hinj, i2597 hinj, i2598 hinj, i2290 hinj] at h
  linarith

theorem row970 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3735 + (1 : ℝ) * HLm Γ 5 L4108 + (-1 : ℝ) * HLm Γ 5 L4634 + (-1 : ℝ) * HLm Γ 5 L4162 := by
  have h := HLm_submod hΓ [F1] L4163 [F27]
  rw [show [F1] ++ L4163 ++ [F27] = L4635 from rfl, show [F1] ++ L4163 = L4632 from rfl,
    show L4163 ++ [F27] = L4633 from rfl] at h
  rw [i2602 hinj, i2600 hinj, i2601 hinj, i2325 hinj] at h
  linarith

theorem row971 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L851 + (1 : ℝ) * HLm Γ 5 L3683 + (-1 : ℝ) * HLm Γ 5 L3517 + (-1 : ℝ) * HLm Γ 5 L1480 := by
  have h := HLm_submod hΓ [F0] L1481 [F218]
  rw [show [F0] ++ L1481 ++ [F218] = L4637 from rfl, show [F0] ++ L1481 = L1476 from rfl,
    show L1481 ++ [F218] = L4636 from rfl] at h
  rw [i2604 hinj, i746 hinj, i2603 hinj, i749 hinj] at h
  linarith

theorem row972 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4638 + (1 : ℝ) * HLm Γ 5 L3442 + (-1 : ℝ) * HLm Γ 5 L2658 + (-1 : ℝ) * HLm Γ 5 L4642 := by
  have h := HLm_submod hΓ [F16] L4643 [F25]
  rw [show [F16] ++ L4643 ++ [F25] = L4641 from rfl, show [F16] ++ L4643 = L4639 from rfl,
    show L4643 ++ [F25] = L4640 from rfl] at h
  rw [i2607 hinj, i2605 hinj, i2606 hinj, i2608 hinj] at h
  linarith

theorem row973 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4151 + (1 : ℝ) * HLm Γ 5 L3453 + (-1 : ℝ) * HLm Γ 5 L4646 + (-1 : ℝ) * HLm Γ 5 L3449 := by
  have h := HLm_submod hΓ [F7] L4648 [F214]
  rw [show [F7] ++ L4648 ++ [F214] = L4647 from rfl, show [F7] ++ L4648 = L4644 from rfl,
    show L4648 ++ [F214] = L4645 from rfl] at h
  rw [i2611 hinj, i2609 hinj, i2610 hinj, i2612 hinj] at h
  linarith

theorem row974 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4649 + (1 : ℝ) * HLm Γ 5 L4651 + (-1 : ℝ) * HLm Γ 5 L4653 + (-1 : ℝ) * HLm Γ 5 L4655 := by
  have h := HLm_submod hΓ [F214] L4656 [F17]
  rw [show [F214] ++ L4656 ++ [F17] = L4654 from rfl, show [F214] ++ L4656 = L4650 from rfl,
    show L4656 ++ [F17] = L4652 from rfl] at h
  rw [i2615 hinj, i2613 hinj, i2614 hinj, i2616 hinj] at h
  linarith

theorem row975 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4657 + (1 : ℝ) * HLm Γ 5 L4659 + (-1 : ℝ) * HLm Γ 5 L4661 + (-1 : ℝ) * HLm Γ 5 L4663 := by
  have h := HLm_submod hΓ [F67] L4664 [F210]
  rw [show [F67] ++ L4664 ++ [F210] = L4662 from rfl, show [F67] ++ L4664 = L4658 from rfl,
    show L4664 ++ [F210] = L4660 from rfl] at h
  rw [i2619 hinj, i2617 hinj, i2618 hinj, i2620 hinj] at h
  linarith

theorem row976 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4665 + (1 : ℝ) * HLm Γ 5 L4667 + (-1 : ℝ) * HLm Γ 5 L4669 + (-1 : ℝ) * HLm Γ 5 L3483 := by
  have h := HLm_submod hΓ [F210] L4671 [F6]
  rw [show [F210] ++ L4671 ++ [F6] = L4670 from rfl, show [F210] ++ L4671 = L4666 from rfl,
    show L4671 ++ [F6] = L4668 from rfl] at h
  rw [i2623 hinj, i2621 hinj, i2622 hinj, i2624 hinj] at h
  linarith

theorem row977 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4672 + (1 : ℝ) * HLm Γ 5 L4674 + (-1 : ℝ) * HLm Γ 5 L4676 + (-1 : ℝ) * HLm Γ 5 L4678 := by
  have h := HLm_submod hΓ [F7] L4679 [F6]
  rw [show [F7] ++ L4679 ++ [F6] = L4677 from rfl, show [F7] ++ L4679 = L4673 from rfl,
    show L4679 ++ [F6] = L4675 from rfl] at h
  rw [i2627 hinj, i2625 hinj, i2626 hinj, i2628 hinj] at h
  linarith

theorem row978 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4680 + (1 : ℝ) * HLm Γ 5 L4682 + (-1 : ℝ) * HLm Γ 5 L4684 + (-1 : ℝ) * HLm Γ 5 L3455 := by
  have h := HLm_submod hΓ [F210] L3456 [F36]
  rw [show [F210] ++ L3456 ++ [F36] = L4685 from rfl, show [F210] ++ L3456 = L4681 from rfl,
    show L3456 ++ [F36] = L4683 from rfl] at h
  rw [i2631 hinj, i2629 hinj, i2630 hinj, i1939 hinj] at h
  linarith

theorem row979 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4686 + (1 : ℝ) * HLm Γ 5 L4688 + (-1 : ℝ) * HLm Γ 5 L4690 + (-1 : ℝ) * HLm Γ 5 L208 := by
  have h := HLm_submod hΓ [F210] L209 [F85]
  rw [show [F210] ++ L209 ++ [F85] = L4691 from rfl, show [F210] ++ L209 = L4687 from rfl,
    show L209 ++ [F85] = L4689 from rfl] at h
  rw [i2634 hinj, i2632 hinj, i2633 hinj, i73 hinj] at h
  linarith

theorem row980 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3769 + (1 : ℝ) * HLm Γ 5 L4693 + (-1 : ℝ) * HLm Γ 5 L4695 + (-1 : ℝ) * HLm Γ 5 L3781 := by
  have h := HLm_submod hΓ [F7] L3782 [F85]
  rw [show [F7] ++ L3782 ++ [F85] = L4696 from rfl, show [F7] ++ L3782 = L4692 from rfl,
    show L3782 ++ [F85] = L4694 from rfl] at h
  rw [i2637 hinj, i2635 hinj, i2636 hinj, i2114 hinj] at h
  linarith

theorem row981 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4697 + (1 : ℝ) * HLm Γ 5 L4699 + (-1 : ℝ) * HLm Γ 5 L4701 + (-1 : ℝ) * HLm Γ 5 L4703 := by
  have h := HLm_submod hΓ [F210] L4704 [F34]
  rw [show [F210] ++ L4704 ++ [F34] = L4702 from rfl, show [F210] ++ L4704 = L4698 from rfl,
    show L4704 ++ [F34] = L4700 from rfl] at h
  rw [i2640 hinj, i2638 hinj, i2639 hinj, i2641 hinj] at h
  linarith

theorem row982 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4705 + (1 : ℝ) * HLm Γ 5 L4707 + (-1 : ℝ) * HLm Γ 5 L4709 + (-1 : ℝ) * HLm Γ 5 L4711 := by
  have h := HLm_submod hΓ [F67] L4712 [F36]
  rw [show [F67] ++ L4712 ++ [F36] = L4710 from rfl, show [F67] ++ L4712 = L4706 from rfl,
    show L4712 ++ [F36] = L4708 from rfl] at h
  rw [i2644 hinj, i2642 hinj, i2643 hinj, i2645 hinj] at h
  linarith

theorem row983 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L3465 + (-1 : ℝ) * HLm Γ 5 L4558 + (-1 : ℝ) * HLm Γ 5 L3461 := by
  have h := HLm_submod hΓ [F10] L4716 [F219]
  rw [show [F10] ++ L4716 ++ [F219] = L4715 from rfl, show [F10] ++ L4716 = L4713 from rfl,
    show L4716 ++ [F219] = L4714 from rfl] at h
  rw [i2648 hinj, i2646 hinj, i2647 hinj, i2649 hinj] at h
  linarith

theorem row984 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4717 + (1 : ℝ) * HLm Γ 5 L3472 + (-1 : ℝ) * HLm Γ 5 L4720 + (-1 : ℝ) * HLm Γ 5 L3469 := by
  have h := HLm_submod hΓ [F0] L4722 [F34]
  rw [show [F0] ++ L4722 ++ [F34] = L4721 from rfl, show [F0] ++ L4722 = L4718 from rfl,
    show L4722 ++ [F34] = L4719 from rfl] at h
  rw [i2652 hinj, i2650 hinj, i2651 hinj, i2653 hinj] at h
  linarith

theorem row985 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4723 + (1 : ℝ) * HLm Γ 5 L4020 + (-1 : ℝ) * HLm Γ 5 L4725 + (-1 : ℝ) * HLm Γ 5 L4016 := by
  have h := HLm_submod hΓ [F46] L4017 [F210]
  rw [show [F46] ++ L4017 ++ [F210] = L4726 from rfl, show [F46] ++ L4017 = L4724 from rfl,
    show L4017 ++ [F210] = L4021 from rfl] at h
  rw [i2655 hinj, i2654 hinj, i2244 hinj, i2242 hinj] at h
  linarith

theorem row986 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4727 + (1 : ℝ) * HLm Γ 5 L3479 + (-1 : ℝ) * HLm Γ 5 L4730 + (-1 : ℝ) * HLm Γ 5 L3477 := by
  have h := HLm_submod hΓ [F44] L4732 [F210]
  rw [show [F44] ++ L4732 ++ [F210] = L4731 from rfl, show [F44] ++ L4732 = L4728 from rfl,
    show L4732 ++ [F210] = L4729 from rfl] at h
  rw [i2658 hinj, i2656 hinj, i2657 hinj, i2659 hinj] at h
  linarith

theorem row987 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4733 + (1 : ℝ) * HLm Γ 5 L4667 + (-1 : ℝ) * HLm Γ 5 L4736 + (-1 : ℝ) * HLm Γ 5 L3491 := by
  have h := HLm_submod hΓ [F9] L3492 [F12]
  rw [show [F9] ++ L3492 ++ [F12] = L4737 from rfl, show [F9] ++ L3492 = L4734 from rfl,
    show L3492 ++ [F12] = L4735 from rfl] at h
  rw [i2662 hinj, i2660 hinj, i2661 hinj, i1958 hinj] at h
  linarith

theorem row988 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3487 + (1 : ℝ) * HLm Γ 5 L4738 + (-1 : ℝ) * HLm Γ 5 L4740 + (-1 : ℝ) * HLm Γ 5 L3485 := by
  have h := HLm_submod hΓ [F12] L3486 [F67]
  rw [show [F12] ++ L3486 ++ [F67] = L4741 from rfl, show [F12] ++ L3486 = L3488 from rfl,
    show L3486 ++ [F67] = L4739 from rfl] at h
  rw [i2664 hinj, i1956 hinj, i2663 hinj, i1955 hinj] at h
  linarith

theorem row989 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4742 + (1 : ℝ) * HLm Γ 5 L3503 + (-1 : ℝ) * HLm Γ 5 L4745 + (-1 : ℝ) * HLm Γ 5 L3501 := by
  have h := HLm_submod hΓ [F228] L4747 [F96]
  rw [show [F228] ++ L4747 ++ [F96] = L4746 from rfl, show [F228] ++ L4747 = L4743 from rfl,
    show L4747 ++ [F96] = L4744 from rfl] at h
  rw [i2667 hinj, i2665 hinj, i2666 hinj, i2668 hinj] at h
  linarith

theorem row990 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4748 + (1 : ℝ) * HLm Γ 5 L4750 + (-1 : ℝ) * HLm Γ 5 L4752 + (-1 : ℝ) * HLm Γ 5 L1526 := by
  have h := HLm_submod hΓ [F67] L1527 [F228]
  rw [show [F67] ++ L1527 ++ [F228] = L4753 from rfl, show [F67] ++ L1527 = L4749 from rfl,
    show L1527 ++ [F228] = L4751 from rfl] at h
  rw [i2671 hinj, i2669 hinj, i2670 hinj, i775 hinj] at h
  linarith

theorem row991 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1616 + (1 : ℝ) * HLm Γ 5 L3795 + (-1 : ℝ) * HLm Γ 5 L4756 + (-1 : ℝ) * HLm Γ 5 L4758 := by
  have h := HLm_submod hΓ [F1] L4758 [F217]
  rw [show [F1] ++ L4758 ++ [F217] = L4757 from rfl, show [F1] ++ L4758 = L4754 from rfl,
    show L4758 ++ [F217] = L4755 from rfl] at h
  rw [i2674 hinj, i2672 hinj, i2673 hinj] at h
  linarith

theorem row992 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4759 + (1 : ℝ) * HLm Γ 5 L4761 + (-1 : ℝ) * HLm Γ 5 L4763 + (-1 : ℝ) * HLm Γ 5 L3708 := by
  have h := HLm_submod hΓ [F16] L3709 [F23]
  rw [show [F16] ++ L3709 ++ [F23] = L4764 from rfl, show [F16] ++ L3709 = L4760 from rfl,
    show L3709 ++ [F23] = L4762 from rfl] at h
  rw [i2677 hinj, i2675 hinj, i2676 hinj, i2075 hinj] at h
  linarith

theorem row993 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3795 + (1 : ℝ) * HLm Γ 5 L3712 + (-1 : ℝ) * HLm Γ 5 L4767 + (-1 : ℝ) * HLm Γ 5 L3506 := by
  have h := HLm_submod hΓ [F16] L3506 [F25]
  rw [show [F16] ++ L3506 ++ [F25] = L4768 from rfl, show [F16] ++ L3506 = L4765 from rfl,
    show L3506 ++ [F25] = L4766 from rfl] at h
  rw [i2680 hinj, i2678 hinj, i2679 hinj] at h
  linarith

theorem row994 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3949 + (1 : ℝ) * HLm Γ 5 L3513 + (-1 : ℝ) * HLm Γ 5 L4771 + (-1 : ℝ) * HLm Γ 5 L3511 := by
  have h := HLm_submod hΓ [F16] L3512 [F210]
  rw [show [F16] ++ L3512 ++ [F210] = L4772 from rfl, show [F16] ++ L3512 = L4769 from rfl,
    show L3512 ++ [F210] = L4770 from rfl] at h
  rw [i2683 hinj, i2681 hinj, i2682 hinj, i1969 hinj] at h
  linarith

theorem row995 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3513 + (1 : ℝ) * HLm Γ 5 L4773 + (-1 : ℝ) * HLm Γ 5 L4775 + (-1 : ℝ) * HLm Γ 5 L3511 := by
  have h := HLm_submod hΓ [F210] L3512 [F36]
  rw [show [F210] ++ L3512 ++ [F36] = L4776 from rfl, show [F210] ++ L3512 = L3514 from rfl,
    show L3512 ++ [F36] = L4774 from rfl] at h
  rw [i2685 hinj, i1970 hinj, i2684 hinj, i1969 hinj] at h
  linarith

theorem row996 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4777 + (1 : ℝ) * HLm Γ 5 L4779 + (-1 : ℝ) * HLm Γ 5 L4558 + (-1 : ℝ) * HLm Γ 5 L4782 := by
  have h := HLm_submod hΓ [F0] L4783 [F25]
  rw [show [F0] ++ L4783 ++ [F25] = L4781 from rfl, show [F0] ++ L4783 = L4778 from rfl,
    show L4783 ++ [F25] = L4780 from rfl] at h
  rw [i2688 hinj, i2686 hinj, i2687 hinj, i2689 hinj] at h
  linarith

theorem row997 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1920 + (1 : ℝ) * HLm Γ 5 L4785 + (-1 : ℝ) * HLm Γ 5 L4787 + (-1 : ℝ) * HLm Γ 5 L4789 := by
  have h := HLm_submod hΓ [F4] L4790 [F228]
  rw [show [F4] ++ L4790 ++ [F228] = L4788 from rfl, show [F4] ++ L4790 = L4784 from rfl,
    show L4790 ++ [F228] = L4786 from rfl] at h
  rw [i2692 hinj, i2690 hinj, i2691 hinj, i2693 hinj] at h
  linarith

theorem row998 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4791 + (1 : ℝ) * HLm Γ 5 L4793 + (-1 : ℝ) * HLm Γ 5 L4441 + (-1 : ℝ) * HLm Γ 5 L4796 := by
  have h := HLm_submod hΓ [F0] L4797 [F6]
  rw [show [F0] ++ L4797 ++ [F6] = L4795 from rfl, show [F0] ++ L4797 = L4792 from rfl,
    show L4797 ++ [F6] = L4794 from rfl] at h
  rw [i2696 hinj, i2694 hinj, i2695 hinj, i2697 hinj] at h
  linarith

theorem row999 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4798 + (1 : ℝ) * HLm Γ 5 L3530 + (-1 : ℝ) * HLm Γ 5 L4801 + (-1 : ℝ) * HLm Γ 5 L3524 := by
  have h := HLm_submod hΓ [F1] L3525 [F67]
  rw [show [F1] ++ L3525 ++ [F67] = L4802 from rfl, show [F1] ++ L3525 = L4799 from rfl,
    show L3525 ++ [F67] = L4800 from rfl] at h
  rw [i2700 hinj, i2698 hinj, i2699 hinj, i1977 hinj] at h
  linarith

theorem row1000 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4803 + (1 : ℝ) * HLm Γ 5 L4805 + (-1 : ℝ) * HLm Γ 5 L4807 + (-1 : ℝ) * HLm Γ 5 L4809 := by
  have h := HLm_submod hΓ [F210] L4810 [F33]
  rw [show [F210] ++ L4810 ++ [F33] = L4808 from rfl, show [F210] ++ L4810 = L4804 from rfl,
    show L4810 ++ [F33] = L4806 from rfl] at h
  rw [i2703 hinj, i2701 hinj, i2702 hinj, i2704 hinj] at h
  linarith

theorem row1001 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4811 + (1 : ℝ) * HLm Γ 5 L3556 + (-1 : ℝ) * HLm Γ 5 L4814 + (-1 : ℝ) * HLm Γ 5 L3554 := by
  have h := HLm_submod hΓ [F67] L3555 [F25]
  rw [show [F67] ++ L3555 ++ [F25] = L4815 from rfl, show [F67] ++ L3555 = L4812 from rfl,
    show L3555 ++ [F25] = L4813 from rfl] at h
  rw [i2707 hinj, i2705 hinj, i2706 hinj, i1992 hinj] at h
  linarith

theorem row1002 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2241 + (1 : ℝ) * HLm Γ 5 L3550 + (-1 : ℝ) * HLm Γ 5 L4818 + (-1 : ℝ) * HLm Γ 5 L2409 := by
  have h := HLm_submod hΓ [F0] L4820 [F210]
  rw [show [F0] ++ L4820 ++ [F210] = L4819 from rfl, show [F0] ++ L4820 = L4816 from rfl,
    show L4820 ++ [F210] = L4817 from rfl] at h
  rw [i2710 hinj, i2708 hinj, i2709 hinj, i2711 hinj] at h
  linarith

theorem row1003 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L863 + (1 : ℝ) * HLm Γ 5 L3550 + (-1 : ℝ) * HLm Γ 5 L4822 + (-1 : ℝ) * HLm Γ 5 L2409 := by
  have h := HLm_submod hΓ [F12] L4820 [F210]
  rw [show [F12] ++ L4820 ++ [F210] = L4823 from rfl, show [F12] ++ L4820 = L4821 from rfl,
    show L4820 ++ [F210] = L4817 from rfl] at h
  rw [i2713 hinj, i2712 hinj, i2709 hinj, i2711 hinj] at h
  linarith

theorem row1004 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L863 + (1 : ℝ) * HLm Γ 5 L4824 + (-1 : ℝ) * HLm Γ 5 L4826 + (-1 : ℝ) * HLm Γ 5 L2409 := by
  have h := HLm_submod hΓ [F12] L4820 [F228]
  rw [show [F12] ++ L4820 ++ [F228] = L4827 from rfl, show [F12] ++ L4820 = L4821 from rfl,
    show L4820 ++ [F228] = L4825 from rfl] at h
  rw [i2715 hinj, i2712 hinj, i2714 hinj, i2711 hinj] at h
  linarith

theorem row1005 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4554 + (1 : ℝ) * HLm Γ 5 L3613 + (-1 : ℝ) * HLm Γ 5 L4317 + (-1 : ℝ) * HLm Γ 5 L3611 := by
  have h := HLm_submod hΓ [F0] L4831 [F1]
  rw [show [F0] ++ L4831 ++ [F1] = L4830 from rfl, show [F0] ++ L4831 = L4828 from rfl,
    show L4831 ++ [F1] = L4829 from rfl] at h
  rw [i2718 hinj, i2716 hinj, i2717 hinj, i2719 hinj] at h
  linarith

theorem row1006 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4832 + (1 : ℝ) * HLm Γ 5 L3583 + (-1 : ℝ) * HLm Γ 5 L4835 + (-1 : ℝ) * HLm Γ 5 L4837 := by
  have h := HLm_submod hΓ [F0] L4838 [F55]
  rw [show [F0] ++ L4838 ++ [F55] = L4836 from rfl, show [F0] ++ L4838 = L4833 from rfl,
    show L4838 ++ [F55] = L4834 from rfl] at h
  rw [i2722 hinj, i2720 hinj, i2721 hinj, i2723 hinj] at h
  linarith

theorem row1007 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L338 + (1 : ℝ) * HLm Γ 5 L4840 + (-1 : ℝ) * HLm Γ 5 L4842 + (-1 : ℝ) * HLm Γ 5 L3575 := by
  have h := HLm_submod hΓ [F0] L4844 [F210]
  rw [show [F0] ++ L4844 ++ [F210] = L4843 from rfl, show [F0] ++ L4844 = L4839 from rfl,
    show L4844 ++ [F210] = L4841 from rfl] at h
  rw [i2726 hinj, i2724 hinj, i2725 hinj, i2727 hinj] at h
  linarith

theorem row1008 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4845 + (1 : ℝ) * HLm Γ 5 L4847 + (-1 : ℝ) * HLm Γ 5 L4849 + (-1 : ℝ) * HLm Γ 5 L2103 := by
  have h := HLm_submod hΓ [F210] L4851 [F17]
  rw [show [F210] ++ L4851 ++ [F17] = L4850 from rfl, show [F210] ++ L4851 = L4846 from rfl,
    show L4851 ++ [F17] = L4848 from rfl] at h
  rw [i2730 hinj, i2728 hinj, i2729 hinj, i2731 hinj] at h
  linarith

theorem row1009 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4852 + (1 : ℝ) * HLm Γ 5 L4854 + (-1 : ℝ) * HLm Γ 5 L4856 + (-1 : ℝ) * HLm Γ 5 L2329 := by
  have h := HLm_submod hΓ [F211] L4858 [F96]
  rw [show [F211] ++ L4858 ++ [F96] = L4857 from rfl, show [F211] ++ L4858 = L4853 from rfl,
    show L4858 ++ [F96] = L4855 from rfl] at h
  rw [i2734 hinj, i2732 hinj, i2733 hinj, i2735 hinj] at h
  linarith

theorem row1010 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4859 + (1 : ℝ) * HLm Γ 5 L4861 + (-1 : ℝ) * HLm Γ 5 L4863 + (-1 : ℝ) * HLm Γ 5 L4865 := by
  have h := HLm_submod hΓ [F2] L4866 [F228]
  rw [show [F2] ++ L4866 ++ [F228] = L4864 from rfl, show [F2] ++ L4866 = L4860 from rfl,
    show L4866 ++ [F228] = L4862 from rfl] at h
  rw [i2738 hinj, i2736 hinj, i2737 hinj, i2739 hinj] at h
  linarith

theorem row1011 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4867 + (1 : ℝ) * HLm Γ 5 L4869 + (-1 : ℝ) * HLm Γ 5 L4871 + (-1 : ℝ) * HLm Γ 5 L3003 := by
  have h := HLm_submod hΓ [F228] L3004 [F96]
  rw [show [F228] ++ L3004 ++ [F96] = L4872 from rfl, show [F228] ++ L3004 = L4868 from rfl,
    show L3004 ++ [F96] = L4870 from rfl] at h
  rw [i2742 hinj, i2740 hinj, i2741 hinj, i1711 hinj] at h
  linarith

theorem row1012 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4873 + (1 : ℝ) * HLm Γ 5 L4875 + (-1 : ℝ) * HLm Γ 5 L4877 + (-1 : ℝ) * HLm Γ 5 L4024 := by
  have h := HLm_submod hΓ [F210] L4025 [F43]
  rw [show [F210] ++ L4025 ++ [F43] = L4878 from rfl, show [F210] ++ L4025 = L4874 from rfl,
    show L4025 ++ [F43] = L4876 from rfl] at h
  rw [i2745 hinj, i2743 hinj, i2744 hinj, i2246 hinj] at h
  linarith

theorem row1013 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4507 + (1 : ℝ) * HLm Γ 5 L4880 + (-1 : ℝ) * HLm Γ 5 L4882 + (-1 : ℝ) * HLm Γ 5 L4884 := by
  have h := HLm_submod hΓ [F0] L4885 [F5]
  rw [show [F0] ++ L4885 ++ [F5] = L4883 from rfl, show [F0] ++ L4885 = L4879 from rfl,
    show L4885 ++ [F5] = L4881 from rfl] at h
  rw [i2748 hinj, i2746 hinj, i2747 hinj, i2749 hinj] at h
  linarith

theorem row1014 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3616 + (1 : ℝ) * HLm Γ 5 L3704 + (-1 : ℝ) * HLm Γ 5 L4888 + (-1 : ℝ) * HLm Γ 5 L4041 := by
  have h := HLm_submod hΓ [F0] L4890 [F3]
  rw [show [F0] ++ L4890 ++ [F3] = L4889 from rfl, show [F0] ++ L4890 = L4886 from rfl,
    show L4890 ++ [F3] = L4887 from rfl] at h
  rw [i2752 hinj, i2750 hinj, i2751 hinj, i2753 hinj] at h
  linarith

theorem row1015 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4891 + (1 : ℝ) * HLm Γ 5 L4893 + (-1 : ℝ) * HLm Γ 5 L4895 + (-1 : ℝ) * HLm Γ 5 L4897 := by
  have h := HLm_submod hΓ [F1] L4898 [F6]
  rw [show [F1] ++ L4898 ++ [F6] = L4896 from rfl, show [F1] ++ L4898 = L4892 from rfl,
    show L4898 ++ [F6] = L4894 from rfl] at h
  rw [i2756 hinj, i2754 hinj, i2755 hinj, i2757 hinj] at h
  linarith

theorem row1016 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3616 + (1 : ℝ) * HLm Γ 5 L4900 + (-1 : ℝ) * HLm Γ 5 L4902 + (-1 : ℝ) * HLm Γ 5 L3598 := by
  have h := HLm_submod hΓ [F0] L4904 [F96]
  rw [show [F0] ++ L4904 ++ [F96] = L4903 from rfl, show [F0] ++ L4904 = L4899 from rfl,
    show L4904 ++ [F96] = L4901 from rfl] at h
  rw [i2760 hinj, i2758 hinj, i2759 hinj, i2761 hinj] at h
  linarith

theorem row1017 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3279 + (1 : ℝ) * HLm Γ 5 L4906 + (-1 : ℝ) * HLm Γ 5 L4522 + (-1 : ℝ) * HLm Γ 5 L4070 := by
  have h := HLm_submod hΓ [F0] L4071 [F96]
  rw [show [F0] ++ L4071 ++ [F96] = L4908 from rfl, show [F0] ++ L4071 = L4905 from rfl,
    show L4071 ++ [F96] = L4907 from rfl] at h
  rw [i2764 hinj, i2762 hinj, i2763 hinj, i2271 hinj] at h
  linarith

theorem row1018 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3573 + (1 : ℝ) * HLm Γ 5 L4910 + (-1 : ℝ) * HLm Γ 5 L4912 + (-1 : ℝ) * HLm Γ 5 L3571 := by
  have h := HLm_submod hΓ [F67] L4914 [F236]
  rw [show [F67] ++ L4914 ++ [F236] = L4913 from rfl, show [F67] ++ L4914 = L4909 from rfl,
    show L4914 ++ [F236] = L4911 from rfl] at h
  rw [i2767 hinj, i2765 hinj, i2766 hinj, i2768 hinj] at h
  linarith

theorem row1019 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4915 + (1 : ℝ) * HLm Γ 5 L4917 + (-1 : ℝ) * HLm Γ 5 L4919 + (-1 : ℝ) * HLm Γ 5 L786 := by
  have h := HLm_submod hΓ [F228] L1621 [F43]
  rw [show [F228] ++ L1621 ++ [F43] = L4920 from rfl, show [F228] ++ L1621 = L4916 from rfl,
    show L1621 ++ [F43] = L4918 from rfl] at h
  rw [i2771 hinj, i2769 hinj, i2770 hinj, i834 hinj] at h
  linarith

theorem row1020 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4921 + (1 : ℝ) * HLm Γ 5 L4159 + (-1 : ℝ) * HLm Γ 5 L4923 + (-1 : ℝ) * HLm Γ 5 L3592 := by
  have h := HLm_submod hΓ [F23] L4157 [F210]
  rw [show [F23] ++ L4157 ++ [F210] = L4924 from rfl, show [F23] ++ L4157 = L4922 from rfl,
    show L4157 ++ [F210] = L4160 from rfl] at h
  rw [i2773 hinj, i2772 hinj, i2323 hinj, i2321 hinj] at h
  linarith

theorem row1021 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3569 + (1 : ℝ) * HLm Γ 5 L4925 + (-1 : ℝ) * HLm Γ 5 L4927 + (-1 : ℝ) * HLm Γ 5 L3567 := by
  have h := HLm_submod hΓ [F0] L3568 [F43]
  rw [show [F0] ++ L3568 ++ [F43] = L4928 from rfl, show [F0] ++ L3568 = L3570 from rfl,
    show L3568 ++ [F43] = L4926 from rfl] at h
  rw [i2775 hinj, i2001 hinj, i2774 hinj, i2000 hinj] at h
  linarith

theorem row1022 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1469 + (1 : ℝ) * HLm Γ 5 L4930 + (-1 : ℝ) * HLm Γ 5 L4932 + (-1 : ℝ) * HLm Γ 5 L4934 := by
  have h := HLm_submod hΓ [F4] L4935 [F228]
  rw [show [F4] ++ L4935 ++ [F228] = L4933 from rfl, show [F4] ++ L4935 = L4929 from rfl,
    show L4935 ++ [F228] = L4931 from rfl] at h
  rw [i2778 hinj, i2776 hinj, i2777 hinj, i2779 hinj] at h
  linarith

theorem row1023 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4936 + (1 : ℝ) * HLm Γ 5 L4036 + (-1 : ℝ) * HLm Γ 5 L4939 + (-1 : ℝ) * HLm Γ 5 L3587 := by
  have h := HLm_submod hΓ [F2] L4941 [F211]
  rw [show [F2] ++ L4941 ++ [F211] = L4940 from rfl, show [F2] ++ L4941 = L4937 from rfl,
    show L4941 ++ [F211] = L4938 from rfl] at h
  rw [i2782 hinj, i2780 hinj, i2781 hinj, i2783 hinj] at h
  linarith

theorem row1024 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3604 + (1 : ℝ) * HLm Γ 5 L4028 + (-1 : ℝ) * HLm Γ 5 L4944 + (-1 : ℝ) * HLm Γ 5 L3602 := by
  have h := HLm_submod hΓ [F0] L4946 [F23]
  rw [show [F0] ++ L4946 ++ [F23] = L4945 from rfl, show [F0] ++ L4946 = L4942 from rfl,
    show L4946 ++ [F23] = L4943 from rfl] at h
  rw [i2786 hinj, i2784 hinj, i2785 hinj, i2787 hinj] at h
  linarith

theorem row1025 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2670 + (1 : ℝ) * HLm Γ 5 L4295 + (-1 : ℝ) * HLm Γ 5 L4949 + (-1 : ℝ) * HLm Γ 5 L839 := by
  have h := HLm_submod hΓ [F16] L4951 [F210]
  rw [show [F16] ++ L4951 ++ [F210] = L4950 from rfl, show [F16] ++ L4951 = L4947 from rfl,
    show L4951 ++ [F210] = L4948 from rfl] at h
  rw [i2790 hinj, i2788 hinj, i2789 hinj, i2791 hinj] at h
  linarith

theorem row1026 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4952 + (1 : ℝ) * HLm Γ 5 L3641 + (-1 : ℝ) * HLm Γ 5 L4955 + (-1 : ℝ) * HLm Γ 5 L3637 := by
  have h := HLm_submod hΓ [F36] L4957 [F219]
  rw [show [F36] ++ L4957 ++ [F219] = L4956 from rfl, show [F36] ++ L4957 = L4953 from rfl,
    show L4957 ++ [F219] = L4954 from rfl] at h
  rw [i2794 hinj, i2792 hinj, i2793 hinj, i2795 hinj] at h
  linarith

theorem row1027 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4958 + (1 : ℝ) * HLm Γ 5 L4960 + (-1 : ℝ) * HLm Γ 5 L4962 + (-1 : ℝ) * HLm Γ 5 L4964 := by
  have h := HLm_submod hΓ [F210] L4965 [F36]
  rw [show [F210] ++ L4965 ++ [F36] = L4963 from rfl, show [F210] ++ L4965 = L4959 from rfl,
    show L4965 ++ [F36] = L4961 from rfl] at h
  rw [i2798 hinj, i2796 hinj, i2797 hinj, i2799 hinj] at h
  linarith

theorem row1028 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4966 + (1 : ℝ) * HLm Γ 5 L4968 + (-1 : ℝ) * HLm Γ 5 L4970 + (-1 : ℝ) * HLm Γ 5 L3639 := by
  have h := HLm_submod hΓ [F67] L3640 [F27]
  rw [show [F67] ++ L3640 ++ [F27] = L4971 from rfl, show [F67] ++ L3640 = L4967 from rfl,
    show L3640 ++ [F27] = L4969 from rfl] at h
  rw [i2802 hinj, i2800 hinj, i2801 hinj, i2039 hinj] at h
  linarith

theorem row1029 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4972 + (1 : ℝ) * HLm Γ 5 L4974 + (-1 : ℝ) * HLm Γ 5 L4976 + (-1 : ℝ) * HLm Γ 5 L4172 := by
  have h := HLm_submod hΓ [F62] L4978 [F67]
  rw [show [F62] ++ L4978 ++ [F67] = L4977 from rfl, show [F62] ++ L4978 = L4973 from rfl,
    show L4978 ++ [F67] = L4975 from rfl] at h
  rw [i2805 hinj, i2803 hinj, i2804 hinj, i2806 hinj] at h
  linarith

theorem row1030 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3382 + (1 : ℝ) * HLm Γ 5 L3889 + (-1 : ℝ) * HLm Γ 5 L4980 + (-1 : ℝ) * HLm Γ 5 L883 := by
  have h := HLm_submod hΓ [F7] L3888 [F210]
  rw [show [F7] ++ L3888 ++ [F210] = L4981 from rfl, show [F7] ++ L3888 = L4979 from rfl,
    show L3888 ++ [F210] = L3890 from rfl] at h
  rw [i2808 hinj, i2807 hinj, i2173 hinj, i2172 hinj] at h
  linarith

theorem row1031 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3648 + (1 : ℝ) * HLm Γ 5 L4982 + (-1 : ℝ) * HLm Γ 5 L4984 + (-1 : ℝ) * HLm Γ 5 L3646 := by
  have h := HLm_submod hΓ [F7] L3647 [F55]
  rw [show [F7] ++ L3647 ++ [F55] = L4985 from rfl, show [F7] ++ L3647 = L3649 from rfl,
    show L3647 ++ [F55] = L4983 from rfl] at h
  rw [i2810 hinj, i2043 hinj, i2809 hinj, i2042 hinj] at h
  linarith

theorem row1032 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4986 + (1 : ℝ) * HLm Γ 5 L3656 + (-1 : ℝ) * HLm Γ 5 L4989 + (-1 : ℝ) * HLm Γ 5 L3654 := by
  have h := HLm_submod hΓ [F7] L3654 [F16]
  rw [show [F7] ++ L3654 ++ [F16] = L4990 from rfl, show [F7] ++ L3654 = L4987 from rfl,
    show L3654 ++ [F16] = L4988 from rfl] at h
  rw [i2813 hinj, i2811 hinj, i2812 hinj] at h
  linarith

theorem row1033 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4991 + (1 : ℝ) * HLm Γ 5 L4993 + (-1 : ℝ) * HLm Γ 5 L4995 + (-1 : ℝ) * HLm Γ 5 L4997 := by
  have h := HLm_submod hΓ [F210] L4997 [F36]
  rw [show [F210] ++ L4997 ++ [F36] = L4996 from rfl, show [F210] ++ L4997 = L4992 from rfl,
    show L4997 ++ [F36] = L4994 from rfl] at h
  rw [i2816 hinj, i2814 hinj, i2815 hinj] at h
  linarith

theorem row1034 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4998 + (1 : ℝ) * HLm Γ 5 L5000 + (-1 : ℝ) * HLm Γ 5 L5002 + (-1 : ℝ) * HLm Γ 5 L3662 := by
  have h := HLm_submod hΓ [F210] L3662 [F33]
  rw [show [F210] ++ L3662 ++ [F33] = L5003 from rfl, show [F210] ++ L3662 = L4999 from rfl,
    show L3662 ++ [F33] = L5001 from rfl] at h
  rw [i2819 hinj, i2817 hinj, i2818 hinj] at h
  linarith

theorem row1035 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5004 + (1 : ℝ) * HLm Γ 5 L5006 + (-1 : ℝ) * HLm Γ 5 L5008 + (-1 : ℝ) * HLm Γ 5 L5010 := by
  have h := HLm_submod hΓ [F67] L5011 [F96]
  rw [show [F67] ++ L5011 ++ [F96] = L5009 from rfl, show [F67] ++ L5011 = L5005 from rfl,
    show L5011 ++ [F96] = L5007 from rfl] at h
  rw [i2822 hinj, i2820 hinj, i2821 hinj, i2823 hinj] at h
  linarith

theorem row1036 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5012 + (1 : ℝ) * HLm Γ 5 L5014 + (-1 : ℝ) * HLm Γ 5 L5016 + (-1 : ℝ) * HLm Γ 5 L5018 := by
  have h := HLm_submod hΓ [F67] L5019 [F36]
  rw [show [F67] ++ L5019 ++ [F36] = L5017 from rfl, show [F67] ++ L5019 = L5013 from rfl,
    show L5019 ++ [F36] = L5015 from rfl] at h
  rw [i2826 hinj, i2824 hinj, i2825 hinj, i2827 hinj] at h
  linarith

theorem row1037 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5020 + (1 : ℝ) * HLm Γ 5 L5022 + (-1 : ℝ) * HLm Γ 5 L5024 + (-1 : ℝ) * HLm Γ 5 L5026 := by
  have h := HLm_submod hΓ [F17] L5027 [F219]
  rw [show [F17] ++ L5027 ++ [F219] = L5025 from rfl, show [F17] ++ L5027 = L5021 from rfl,
    show L5027 ++ [F219] = L5023 from rfl] at h
  rw [i2830 hinj, i2828 hinj, i2829 hinj, i2831 hinj] at h
  linarith

theorem row1038 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5028 + (1 : ℝ) * HLm Γ 5 L5030 + (-1 : ℝ) * HLm Γ 5 L5032 + (-1 : ℝ) * HLm Γ 5 L3694 := by
  have h := HLm_submod hΓ [F68] L3695 [F210]
  rw [show [F68] ++ L3695 ++ [F210] = L5033 from rfl, show [F68] ++ L3695 = L5029 from rfl,
    show L3695 ++ [F210] = L5031 from rfl] at h
  rw [i2834 hinj, i2832 hinj, i2833 hinj, i2068 hinj] at h
  linarith

theorem row1039 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5034 + (1 : ℝ) * HLm Γ 5 L5036 + (-1 : ℝ) * HLm Γ 5 L5038 + (-1 : ℝ) * HLm Γ 5 L5040 := by
  have h := HLm_submod hΓ [F210] L5041 [F90]
  rw [show [F210] ++ L5041 ++ [F90] = L5039 from rfl, show [F210] ++ L5041 = L5035 from rfl,
    show L5041 ++ [F90] = L5037 from rfl] at h
  rw [i2837 hinj, i2835 hinj, i2836 hinj, i2838 hinj] at h
  linarith

theorem row1040 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5042 + (1 : ℝ) * HLm Γ 5 L5044 + (-1 : ℝ) * HLm Γ 5 L5046 + (-1 : ℝ) * HLm Γ 5 L3968 := by
  have h := HLm_submod hΓ [F210] L3969 [F43]
  rw [show [F210] ++ L3969 ++ [F43] = L5047 from rfl, show [F210] ++ L3969 = L5043 from rfl,
    show L3969 ++ [F43] = L5045 from rfl] at h
  rw [i2841 hinj, i2839 hinj, i2840 hinj, i2215 hinj] at h
  linarith

theorem row1041 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3717 + (1 : ℝ) * HLm Γ 5 L5049 + (-1 : ℝ) * HLm Γ 5 L5051 + (-1 : ℝ) * HLm Γ 5 L3715 := by
  have h := HLm_submod hΓ [F22] L5053 [F214]
  rw [show [F22] ++ L5053 ++ [F214] = L5052 from rfl, show [F22] ++ L5053 = L5048 from rfl,
    show L5053 ++ [F214] = L5050 from rfl] at h
  rw [i2844 hinj, i2842 hinj, i2843 hinj, i2845 hinj] at h
  linarith

theorem row1042 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5054 + (1 : ℝ) * HLm Γ 5 L3696 + (-1 : ℝ) * HLm Γ 5 L5057 + (-1 : ℝ) * HLm Γ 5 L3702 := by
  have h := HLm_submod hΓ [F0] L3703 [F5]
  rw [show [F0] ++ L3703 ++ [F5] = L5058 from rfl, show [F0] ++ L3703 = L5055 from rfl,
    show L3703 ++ [F5] = L5056 from rfl] at h
  rw [i2848 hinj, i2846 hinj, i2847 hinj, i2072 hinj] at h
  linarith

theorem row1043 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3727 + (1 : ℝ) * HLm Γ 5 L5060 + (-1 : ℝ) * HLm Γ 5 L5062 + (-1 : ℝ) * HLm Γ 5 L3725 := by
  have h := HLm_submod hΓ [F9] L5064 [F5]
  rw [show [F9] ++ L5064 ++ [F5] = L5063 from rfl, show [F9] ++ L5064 = L5059 from rfl,
    show L5064 ++ [F5] = L5061 from rfl] at h
  rw [i2851 hinj, i2849 hinj, i2850 hinj, i2852 hinj] at h
  linarith

theorem row1044 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3651 + (1 : ℝ) * HLm Γ 5 L3689 + (-1 : ℝ) * HLm Γ 5 L5067 + (-1 : ℝ) * HLm Γ 5 L3710 := by
  have h := HLm_submod hΓ [F47] L3711 [F16]
  rw [show [F47] ++ L3711 ++ [F16] = L5068 from rfl, show [F47] ++ L3711 = L5065 from rfl,
    show L3711 ++ [F16] = L5066 from rfl] at h
  rw [i2855 hinj, i2853 hinj, i2854 hinj, i2076 hinj] at h
  linarith

theorem row1045 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2376 + (1 : ℝ) * HLm Γ 5 L4130 + (-1 : ℝ) * HLm Γ 5 L5070 + (-1 : ℝ) * HLm Γ 5 L4127 := by
  have h := HLm_submod hΓ [F47] L4128 [F228]
  rw [show [F47] ++ L4128 ++ [F228] = L5071 from rfl, show [F47] ++ L4128 = L5069 from rfl,
    show L4128 ++ [F228] = L4131 from rfl] at h
  rw [i2857 hinj, i2856 hinj, i2306 hinj, i2304 hinj] at h
  linarith

theorem row1046 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5072 + (1 : ℝ) * HLm Γ 5 L5074 + (-1 : ℝ) * HLm Γ 5 L5076 + (-1 : ℝ) * HLm Γ 5 L3737 := by
  have h := HLm_submod hΓ [F67] L5078 [F210]
  rw [show [F67] ++ L5078 ++ [F210] = L5077 from rfl, show [F67] ++ L5078 = L5073 from rfl,
    show L5078 ++ [F210] = L5075 from rfl] at h
  rw [i2860 hinj, i2858 hinj, i2859 hinj, i2861 hinj] at h
  linarith

theorem row1047 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5079 + (1 : ℝ) * HLm Γ 5 L5081 + (-1 : ℝ) * HLm Γ 5 L5083 + (-1 : ℝ) * HLm Γ 5 L5085 := by
  have h := HLm_submod hΓ [F7] L5086 [F67]
  rw [show [F7] ++ L5086 ++ [F67] = L5084 from rfl, show [F7] ++ L5086 = L5080 from rfl,
    show L5086 ++ [F67] = L5082 from rfl] at h
  rw [i2864 hinj, i2862 hinj, i2863 hinj, i2865 hinj] at h
  linarith

theorem row1048 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5087 + (1 : ℝ) * HLm Γ 5 L5089 + (-1 : ℝ) * HLm Γ 5 L5091 + (-1 : ℝ) * HLm Γ 5 L516 := by
  have h := HLm_submod hΓ [F47] L907 [F217]
  rw [show [F47] ++ L907 ++ [F217] = L5092 from rfl, show [F47] ++ L907 = L5088 from rfl,
    show L907 ++ [F217] = L5090 from rfl] at h
  rw [i2868 hinj, i2866 hinj, i2867 hinj, i416 hinj] at h
  linarith

theorem row1049 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5093 + (1 : ℝ) * HLm Γ 5 L5095 + (-1 : ℝ) * HLm Γ 5 L5097 + (-1 : ℝ) * HLm Γ 5 L3761 := by
  have h := HLm_submod hΓ [F47] L3762 [F210]
  rw [show [F47] ++ L3762 ++ [F210] = L5098 from rfl, show [F47] ++ L3762 = L5094 from rfl,
    show L3762 ++ [F210] = L5096 from rfl] at h
  rw [i2871 hinj, i2869 hinj, i2870 hinj, i2102 hinj] at h
  linarith

end EntropyBounds.TwoSet.Certs.R7A5
