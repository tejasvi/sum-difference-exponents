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

theorem row750 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3411 + (1 : ℝ) * HLm Γ 5 L3413 + (-1 : ℝ) * HLm Γ 5 L3415 + (-1 : ℝ) * HLm Γ 5 L3417 := by
  have h := HLm_submod hΓ [F16] L3418 [F17]
  rw [show [F16] ++ L3418 ++ [F17] = L3416 from rfl, show [F16] ++ L3418 = L3412 from rfl,
    show L3418 ++ [F17] = L3414 from rfl] at h
  rw [i1917 hinj, i1915 hinj, i1916 hinj, i1918 hinj] at h
  linarith

theorem row751 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3419 + (1 : ℝ) * HLm Γ 5 L3421 + (-1 : ℝ) * HLm Γ 5 L3423 + (-1 : ℝ) * HLm Γ 5 L3425 := by
  have h := HLm_submod hΓ [F9] L3426 [F43]
  rw [show [F9] ++ L3426 ++ [F43] = L3424 from rfl, show [F9] ++ L3426 = L3420 from rfl,
    show L3426 ++ [F43] = L3422 from rfl] at h
  rw [i1921 hinj, i1919 hinj, i1920 hinj, i1922 hinj] at h
  linarith

theorem row752 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3427 + (1 : ℝ) * HLm Γ 5 L3429 + (-1 : ℝ) * HLm Γ 5 L3431 + (-1 : ℝ) * HLm Γ 5 L126 := by
  have h := HLm_submod hΓ [F67] L2835 [F236]
  rw [show [F67] ++ L2835 ++ [F236] = L3432 from rfl, show [F67] ++ L2835 = L3428 from rfl,
    show L2835 ++ [F236] = L3430 from rfl] at h
  rw [i1925 hinj, i1923 hinj, i1924 hinj, i1628 hinj] at h
  linarith

theorem row753 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3429 + (1 : ℝ) * HLm Γ 5 L3434 + (-1 : ℝ) * HLm Γ 5 L3436 + (-1 : ℝ) * HLm Γ 5 L126 := by
  have h := HLm_submod hΓ [F236] L2835 [F45]
  rw [show [F236] ++ L2835 ++ [F45] = L3437 from rfl, show [F236] ++ L2835 = L3433 from rfl,
    show L2835 ++ [F45] = L3435 from rfl] at h
  rw [i1928 hinj, i1926 hinj, i1927 hinj, i1628 hinj] at h
  linarith

theorem row754 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L222 + (1 : ℝ) * HLm Γ 5 L391 + (-1 : ℝ) * HLm Γ 5 L3439 + (-1 : ℝ) * HLm Γ 5 L388 := by
  have h := HLm_submod hΓ [F1] L389 [F67]
  rw [show [F1] ++ L389 ++ [F67] = L3440 from rfl, show [F1] ++ L389 = L3438 from rfl,
    show L389 ++ [F67] = L392 from rfl] at h
  rw [i1930 hinj, i1929 hinj, i157 hinj, i156 hinj] at h
  linarith

theorem row755 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1480 + (1 : ℝ) * HLm Γ 5 L2885 + (-1 : ℝ) * HLm Γ 5 L3442 + (-1 : ℝ) * HLm Γ 5 L2883 := by
  have h := HLm_submod hΓ [F9] L2883 [F45]
  rw [show [F9] ++ L2883 ++ [F45] = L3443 from rfl, show [F9] ++ L2883 = L3441 from rfl,
    show L2883 ++ [F45] = L2885 from rfl] at h
  rw [i1932 hinj, i1931 hinj] at h
  linarith

theorem row756 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3444 + (1 : ℝ) * HLm Γ 5 L2881 + (-1 : ℝ) * HLm Γ 5 L3447 + (-1 : ℝ) * HLm Γ 5 L2879 := by
  have h := HLm_submod hΓ [F0] L2880 [F67]
  rw [show [F0] ++ L2880 ++ [F67] = L3448 from rfl, show [F0] ++ L2880 = L3445 from rfl,
    show L2880 ++ [F67] = L3446 from rfl] at h
  rw [i1935 hinj, i1933 hinj, i1934 hinj, i1645 hinj] at h
  linarith

theorem row757 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3449 + (1 : ℝ) * HLm Γ 5 L3451 + (-1 : ℝ) * HLm Γ 5 L3453 + (-1 : ℝ) * HLm Γ 5 L724 := by
  have h := HLm_submod hΓ [F68] L725 [F214]
  rw [show [F68] ++ L725 ++ [F214] = L3454 from rfl, show [F68] ++ L725 = L3450 from rfl,
    show L725 ++ [F214] = L3452 from rfl] at h
  rw [i1938 hinj, i1936 hinj, i1937 hinj, i317 hinj] at h
  linarith

theorem row758 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1401 + (1 : ℝ) * HLm Γ 5 L3455 + (-1 : ℝ) * HLm Γ 5 L3457 + (-1 : ℝ) * HLm Γ 5 L3459 := by
  have h := HLm_submod hΓ [F7] L3460 [F6]
  rw [show [F7] ++ L3460 ++ [F6] = L3458 from rfl, show [F7] ++ L3460 = L1402 from rfl,
    show L3460 ++ [F6] = L3456 from rfl] at h
  rw [i1940 hinj, i702 hinj, i1939 hinj, i1941 hinj] at h
  linarith

theorem row759 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3461 + (1 : ℝ) * HLm Γ 5 L3463 + (-1 : ℝ) * HLm Γ 5 L3465 + (-1 : ℝ) * HLm Γ 5 L3467 := by
  have h := HLm_submod hΓ [F96] L3468 [F219]
  rw [show [F96] ++ L3468 ++ [F219] = L3466 from rfl, show [F96] ++ L3468 = L3462 from rfl,
    show L3468 ++ [F219] = L3464 from rfl] at h
  rw [i1944 hinj, i1942 hinj, i1943 hinj, i1945 hinj] at h
  linarith

theorem row760 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3469 + (1 : ℝ) * HLm Γ 5 L2896 + (-1 : ℝ) * HLm Γ 5 L3472 + (-1 : ℝ) * HLm Γ 5 L2893 := by
  have h := HLm_submod hΓ [F211] L3474 [F34]
  rw [show [F211] ++ L3474 ++ [F34] = L3473 from rfl, show [F211] ++ L3474 = L3470 from rfl,
    show L3474 ++ [F34] = L3471 from rfl] at h
  rw [i1948 hinj, i1946 hinj, i1947 hinj, i1949 hinj] at h
  linarith

theorem row761 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3475 + (1 : ℝ) * HLm Γ 5 L3477 + (-1 : ℝ) * HLm Γ 5 L3479 + (-1 : ℝ) * HLm Γ 5 L3481 := by
  have h := HLm_submod hΓ [F210] L3482 [F43]
  rw [show [F210] ++ L3482 ++ [F43] = L3480 from rfl, show [F210] ++ L3482 = L3476 from rfl,
    show L3482 ++ [F43] = L3478 from rfl] at h
  rw [i1952 hinj, i1950 hinj, i1951 hinj, i1953 hinj] at h
  linarith

theorem row762 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3483 + (1 : ℝ) * HLm Γ 5 L3485 + (-1 : ℝ) * HLm Γ 5 L3487 + (-1 : ℝ) * HLm Γ 5 L2895 := by
  have h := HLm_submod hΓ [F12] L2895 [F218]
  rw [show [F12] ++ L2895 ++ [F218] = L3488 from rfl, show [F12] ++ L2895 = L3484 from rfl,
    show L2895 ++ [F218] = L3486 from rfl] at h
  rw [i1956 hinj, i1954 hinj, i1955 hinj] at h
  linarith

theorem row763 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3489 + (1 : ℝ) * HLm Γ 5 L3491 + (-1 : ℝ) * HLm Γ 5 L3493 + (-1 : ℝ) * HLm Γ 5 L2895 := by
  have h := HLm_submod hΓ [F210] L2895 [F6]
  rw [show [F210] ++ L2895 ++ [F6] = L3494 from rfl, show [F210] ++ L2895 = L3490 from rfl,
    show L2895 ++ [F6] = L3492 from rfl] at h
  rw [i1959 hinj, i1957 hinj, i1958 hinj] at h
  linarith

theorem row764 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L851 + (1 : ℝ) * HLm Γ 5 L3496 + (-1 : ℝ) * HLm Γ 5 L1451 + (-1 : ℝ) * HLm Γ 5 L3499 := by
  have h := HLm_submod hΓ [F51] L3500 [F16]
  rw [show [F51] ++ L3500 ++ [F16] = L3498 from rfl, show [F51] ++ L3500 = L3495 from rfl,
    show L3500 ++ [F16] = L3497 from rfl] at h
  rw [i1962 hinj, i1960 hinj, i1961 hinj, i1963 hinj] at h
  linarith

theorem row765 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3501 + (1 : ℝ) * HLm Γ 5 L1526 + (-1 : ℝ) * HLm Γ 5 L3503 + (-1 : ℝ) * HLm Γ 5 L3499 := by
  have h := HLm_submod hΓ [F68] L3500 [F96]
  rw [show [F68] ++ L3500 ++ [F96] = L3504 from rfl, show [F68] ++ L3500 = L3502 from rfl,
    show L3500 ++ [F96] = L1527 from rfl] at h
  rw [i1965 hinj, i1964 hinj, i775 hinj, i1963 hinj] at h
  linarith

theorem row766 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L23 + (1 : ℝ) * HLm Γ 5 L3506 + (-1 : ℝ) * HLm Γ 5 L3507 + (-1 : ℝ) * HLm Γ 5 L2014 := by
  have h := HLm_submod hΓ [F1] L2014 [F217]
  rw [show [F1] ++ L2014 ++ [F217] = L3508 from rfl, show [F1] ++ L2014 = L3505 from rfl,
    show L2014 ++ [F217] = L3506 from rfl] at h
  rw [i1967 hinj, i1966 hinj] at h
  linarith

theorem row767 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3509 + (1 : ℝ) * HLm Γ 5 L3511 + (-1 : ℝ) * HLm Γ 5 L3513 + (-1 : ℝ) * HLm Γ 5 L2014 := by
  have h := HLm_submod hΓ [F210] L2014 [F43]
  rw [show [F210] ++ L2014 ++ [F43] = L3514 from rfl, show [F210] ++ L2014 = L3510 from rfl,
    show L2014 ++ [F43] = L3512 from rfl] at h
  rw [i1970 hinj, i1968 hinj, i1969 hinj] at h
  linarith

theorem row768 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L851 + (1 : ℝ) * HLm Γ 5 L3507 + (-1 : ℝ) * HLm Γ 5 L3517 + (-1 : ℝ) * HLm Γ 5 L23 := by
  have h := HLm_submod hΓ [F0] L24 [F217]
  rw [show [F0] ++ L24 ++ [F217] = L3518 from rfl, show [F0] ++ L24 = L3515 from rfl,
    show L24 ++ [F217] = L3516 from rfl] at h
  rw [i1973 hinj, i1971 hinj, i1972 hinj, i4 hinj] at h
  linarith

theorem row769 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3519 + (1 : ℝ) * HLm Γ 5 L3521 + (-1 : ℝ) * HLm Γ 5 L2813 + (-1 : ℝ) * HLm Γ 5 L159 := by
  have h := HLm_submod hΓ [F4] L763 [F68]
  rw [show [F4] ++ L763 ++ [F68] = L3523 from rfl, show [F4] ++ L763 = L3520 from rfl,
    show L763 ++ [F68] = L3522 from rfl] at h
  rw [i1976 hinj, i1974 hinj, i1975 hinj, i337 hinj] at h
  linarith

theorem row770 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1960 + (1 : ℝ) * HLm Γ 5 L3524 + (-1 : ℝ) * HLm Γ 5 L3526 + (-1 : ℝ) * HLm Γ 5 L2305 := by
  have h := HLm_submod hΓ [F0] L2305 [F219]
  rw [show [F0] ++ L2305 ++ [F219] = L3527 from rfl, show [F0] ++ L2305 = L2300 from rfl,
    show L2305 ++ [F219] = L3525 from rfl] at h
  rw [i1978 hinj, i1269 hinj, i1977 hinj] at h
  linarith

theorem row771 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2314 + (1 : ℝ) * HLm Γ 5 L3529 + (-1 : ℝ) * HLm Γ 5 L3530 + (-1 : ℝ) * HLm Γ 5 L2305 := by
  have h := HLm_submod hΓ [F67] L2305 [F210]
  rw [show [F67] ++ L2305 ++ [F210] = L3531 from rfl, show [F67] ++ L2305 = L3528 from rfl,
    show L2305 ++ [F210] = L3529 from rfl] at h
  rw [i1980 hinj, i1979 hinj] at h
  linarith

theorem row772 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2314 + (1 : ℝ) * HLm Γ 5 L3532 + (-1 : ℝ) * HLm Γ 5 L3533 + (-1 : ℝ) * HLm Γ 5 L2305 := by
  have h := HLm_submod hΓ [F67] L2305 [F214]
  rw [show [F67] ++ L2305 ++ [F214] = L3534 from rfl, show [F67] ++ L2305 = L3528 from rfl,
    show L2305 ++ [F214] = L3532 from rfl] at h
  rw [i1981 hinj, i1979 hinj] at h
  linarith

theorem row773 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3535 + (1 : ℝ) * HLm Γ 5 L3537 + (-1 : ℝ) * HLm Γ 5 L3539 + (-1 : ℝ) * HLm Γ 5 L2305 := by
  have h := HLm_submod hΓ [F82] L2305 [F228]
  rw [show [F82] ++ L2305 ++ [F228] = L3540 from rfl, show [F82] ++ L2305 = L3536 from rfl,
    show L2305 ++ [F228] = L3538 from rfl] at h
  rw [i1984 hinj, i1982 hinj, i1983 hinj] at h
  linarith

theorem row774 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3541 + (1 : ℝ) * HLm Γ 5 L3543 + (-1 : ℝ) * HLm Γ 5 L3545 + (-1 : ℝ) * HLm Γ 5 L168 := by
  have h := HLm_submod hΓ [F68] L769 [F214]
  rw [show [F68] ++ L769 ++ [F214] = L3546 from rfl, show [F68] ++ L769 = L3542 from rfl,
    show L769 ++ [F214] = L3544 from rfl] at h
  rw [i1987 hinj, i1985 hinj, i1986 hinj, i341 hinj] at h
  linarith

theorem row775 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3547 + (1 : ℝ) * HLm Γ 5 L2409 + (-1 : ℝ) * HLm Γ 5 L3550 + (-1 : ℝ) * HLm Γ 5 L168 := by
  have h := HLm_submod hΓ [F210] L769 [F6]
  rw [show [F210] ++ L769 ++ [F6] = L3551 from rfl, show [F210] ++ L769 = L3548 from rfl,
    show L769 ++ [F6] = L3549 from rfl] at h
  rw [i1990 hinj, i1988 hinj, i1989 hinj, i341 hinj] at h
  linarith

theorem row776 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3552 + (1 : ℝ) * HLm Γ 5 L3554 + (-1 : ℝ) * HLm Γ 5 L3556 + (-1 : ℝ) * HLm Γ 5 L168 := by
  have h := HLm_submod hΓ [F25] L769 [F217]
  rw [show [F25] ++ L769 ++ [F217] = L3557 from rfl, show [F25] ++ L769 = L3553 from rfl,
    show L769 ++ [F217] = L3555 from rfl] at h
  rw [i1993 hinj, i1991 hinj, i1992 hinj, i341 hinj] at h
  linarith

theorem row777 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3558 + (1 : ℝ) * HLm Γ 5 L3560 + (-1 : ℝ) * HLm Γ 5 L1105 + (-1 : ℝ) * HLm Γ 5 L25 := by
  have h := HLm_submod hΓ [F2] L25 [F52]
  rw [show [F2] ++ L25 ++ [F52] = L3562 from rfl, show [F2] ++ L25 = L3559 from rfl,
    show L25 ++ [F52] = L3561 from rfl] at h
  rw [i1996 hinj, i1994 hinj, i1995 hinj] at h
  linarith

theorem row778 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3563 + (1 : ℝ) * HLm Γ 5 L3003 + (-1 : ℝ) * HLm Γ 5 L338 + (-1 : ℝ) * HLm Γ 5 L2999 := by
  have h := HLm_submod hΓ [F0] L3000 [F55]
  rw [show [F0] ++ L3000 ++ [F55] = L3565 from rfl, show [F0] ++ L3000 = L3564 from rfl,
    show L3000 ++ [F55] = L3004 from rfl] at h
  rw [i1998 hinj, i1997 hinj, i1711 hinj, i1709 hinj] at h
  linarith

theorem row779 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L74 + (1 : ℝ) * HLm Γ 5 L3567 + (-1 : ℝ) * HLm Γ 5 L3569 + (-1 : ℝ) * HLm Γ 5 L2327 := by
  have h := HLm_submod hΓ [F0] L2328 [F217]
  rw [show [F0] ++ L2328 ++ [F217] = L3570 from rfl, show [F0] ++ L2328 = L3566 from rfl,
    show L2328 ++ [F217] = L3568 from rfl] at h
  rw [i2001 hinj, i1999 hinj, i2000 hinj, i1283 hinj] at h
  linarith

theorem row780 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L790 + (1 : ℝ) * HLm Γ 5 L3571 + (-1 : ℝ) * HLm Γ 5 L3573 + (-1 : ℝ) * HLm Γ 5 L155 := by
  have h := HLm_submod hΓ [F67] L156 [F90]
  rw [show [F67] ++ L156 ++ [F90] = L3574 from rfl, show [F67] ++ L156 = L791 from rfl,
    show L156 ++ [F90] = L3572 from rfl] at h
  rw [i2003 hinj, i353 hinj, i2002 hinj, i50 hinj] at h
  linarith

theorem row781 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3575 + (1 : ℝ) * HLm Γ 5 L3577 + (-1 : ℝ) * HLm Γ 5 L3579 + (-1 : ℝ) * HLm Γ 5 L155 := by
  have h := HLm_submod hΓ [F52] L156 [F236]
  rw [show [F52] ++ L156 ++ [F236] = L3580 from rfl, show [F52] ++ L156 = L3576 from rfl,
    show L156 ++ [F236] = L3578 from rfl] at h
  rw [i2006 hinj, i2004 hinj, i2005 hinj, i50 hinj] at h
  linarith

theorem row782 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3575 + (1 : ℝ) * HLm Γ 5 L3581 + (-1 : ℝ) * HLm Γ 5 L3583 + (-1 : ℝ) * HLm Γ 5 L155 := by
  have h := HLm_submod hΓ [F52] L156 [F214]
  rw [show [F52] ++ L156 ++ [F214] = L3584 from rfl, show [F52] ++ L156 = L3576 from rfl,
    show L156 ++ [F214] = L3582 from rfl] at h
  rw [i2008 hinj, i2004 hinj, i2007 hinj, i50 hinj] at h
  linarith

theorem row783 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3585 + (1 : ℝ) * HLm Γ 5 L3587 + (-1 : ℝ) * HLm Γ 5 L3589 + (-1 : ℝ) * HLm Γ 5 L155 := by
  have h := HLm_submod hΓ [F210] L156 [F6]
  rw [show [F210] ++ L156 ++ [F6] = L3590 from rfl, show [F210] ++ L156 = L3586 from rfl,
    show L156 ++ [F6] = L3588 from rfl] at h
  rw [i2011 hinj, i2009 hinj, i2010 hinj, i50 hinj] at h
  linarith

theorem row784 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L849 + (1 : ℝ) * HLm Γ 5 L3592 + (-1 : ℝ) * HLm Γ 5 L3594 + (-1 : ℝ) * HLm Γ 5 L801 := by
  have h := HLm_submod hΓ [F0] L801 [F96]
  rw [show [F0] ++ L801 ++ [F96] = L3595 from rfl, show [F0] ++ L801 = L3591 from rfl,
    show L801 ++ [F96] = L3593 from rfl] at h
  rw [i2014 hinj, i2012 hinj, i2013 hinj] at h
  linarith

theorem row785 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3596 + (1 : ℝ) * HLm Γ 5 L3598 + (-1 : ℝ) * HLm Γ 5 L3600 + (-1 : ℝ) * HLm Γ 5 L526 := by
  have h := HLm_submod hΓ [F2] L526 [F228]
  rw [show [F2] ++ L526 ++ [F228] = L3601 from rfl, show [F2] ++ L526 = L3597 from rfl,
    show L526 ++ [F228] = L3599 from rfl] at h
  rw [i2017 hinj, i2015 hinj, i2016 hinj] at h
  linarith

theorem row786 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2899 + (1 : ℝ) * HLm Γ 5 L3602 + (-1 : ℝ) * HLm Γ 5 L3604 + (-1 : ℝ) * HLm Γ 5 L2898 := by
  have h := HLm_submod hΓ [F0] L2898 [F55]
  rw [show [F0] ++ L2898 ++ [F55] = L3605 from rfl, show [F0] ++ L2898 = L2900 from rfl,
    show L2898 ++ [F55] = L3603 from rfl] at h
  rw [i2019 hinj, i1655 hinj, i2018 hinj] at h
  linarith

theorem row787 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3606 + (1 : ℝ) * HLm Γ 5 L3184 + (-1 : ℝ) * HLm Γ 5 L3608 + (-1 : ℝ) * HLm Γ 5 L2898 := by
  have h := HLm_submod hΓ [F211] L2898 [F6]
  rw [show [F211] ++ L2898 ++ [F6] = L3609 from rfl, show [F211] ++ L2898 = L3607 from rfl,
    show L2898 ++ [F6] = L3184 from rfl] at h
  rw [i2021 hinj, i2020 hinj] at h
  linarith

theorem row788 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2859 + (1 : ℝ) * HLm Γ 5 L3611 + (-1 : ℝ) * HLm Γ 5 L3613 + (-1 : ℝ) * HLm Γ 5 L2901 := by
  have h := HLm_submod hΓ [F1] L2901 [F22]
  rw [show [F1] ++ L2901 ++ [F22] = L3614 from rfl, show [F1] ++ L2901 = L3610 from rfl,
    show L2901 ++ [F22] = L3612 from rfl] at h
  rw [i2024 hinj, i2022 hinj, i2023 hinj] at h
  linarith

theorem row789 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L831 + (1 : ℝ) * HLm Γ 5 L3616 + (-1 : ℝ) * HLm Γ 5 L3618 + (-1 : ℝ) * HLm Γ 5 L92 := by
  have h := HLm_submod hΓ [F5] L3620 [F210]
  rw [show [F5] ++ L3620 ++ [F210] = L3619 from rfl, show [F5] ++ L3620 = L3615 from rfl,
    show L3620 ++ [F210] = L3617 from rfl] at h
  rw [i2027 hinj, i2025 hinj, i2026 hinj, i2028 hinj] at h
  linarith

theorem row790 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3621 + (1 : ℝ) * HLm Γ 5 L188 + (-1 : ℝ) * HLm Γ 5 L3623 + (-1 : ℝ) * HLm Γ 5 L183 := by
  have h := HLm_submod hΓ [F228] L183 [F45]
  rw [show [F228] ++ L183 ++ [F45] = L3624 from rfl, show [F228] ++ L183 = L3622 from rfl,
    show L183 ++ [F45] = L188 from rfl] at h
  rw [i2030 hinj, i2029 hinj] at h
  linarith

theorem row791 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3625 + (1 : ℝ) * HLm Γ 5 L3627 + (-1 : ℝ) * HLm Γ 5 L3629 + (-1 : ℝ) * HLm Γ 5 L2908 := by
  have h := HLm_submod hΓ [F0] L3631 [F16]
  rw [show [F0] ++ L3631 ++ [F16] = L3630 from rfl, show [F0] ++ L3631 = L3626 from rfl,
    show L3631 ++ [F16] = L3628 from rfl] at h
  rw [i2033 hinj, i2031 hinj, i2032 hinj, i2034 hinj] at h
  linarith

theorem row792 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3632 + (1 : ℝ) * HLm Γ 5 L2911 + (-1 : ℝ) * HLm Γ 5 L3635 + (-1 : ℝ) * HLm Γ 5 L2908 := by
  have h := HLm_submod hΓ [F1] L3631 [F217]
  rw [show [F1] ++ L3631 ++ [F217] = L3636 from rfl, show [F1] ++ L3631 = L3633 from rfl,
    show L3631 ++ [F217] = L3634 from rfl] at h
  rw [i2037 hinj, i2035 hinj, i2036 hinj, i2034 hinj] at h
  linarith

theorem row793 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3637 + (1 : ℝ) * HLm Γ 5 L3639 + (-1 : ℝ) * HLm Γ 5 L3641 + (-1 : ℝ) * HLm Γ 5 L3643 := by
  have h := HLm_submod hΓ [F62] L3643 [F219]
  rw [show [F62] ++ L3643 ++ [F219] = L3642 from rfl, show [F62] ++ L3643 = L3638 from rfl,
    show L3643 ++ [F219] = L3640 from rfl] at h
  rw [i2040 hinj, i2038 hinj, i2039 hinj] at h
  linarith

theorem row794 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3644 + (1 : ℝ) * HLm Γ 5 L3646 + (-1 : ℝ) * HLm Γ 5 L3648 + (-1 : ℝ) * HLm Γ 5 L3650 := by
  have h := HLm_submod hΓ [F7] L3650 [F43]
  rw [show [F7] ++ L3650 ++ [F43] = L3649 from rfl, show [F7] ++ L3650 = L3645 from rfl,
    show L3650 ++ [F43] = L3647 from rfl] at h
  rw [i2043 hinj, i2041 hinj, i2042 hinj] at h
  linarith

theorem row795 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1506 + (1 : ℝ) * HLm Γ 5 L3025 + (-1 : ℝ) * HLm Γ 5 L3651 + (-1 : ℝ) * HLm Γ 5 L2362 := by
  have h := HLm_submod hΓ [F47] L2362 [F217]
  rw [show [F47] ++ L2362 ++ [F217] = L3652 from rfl, show [F47] ++ L2362 = L1507 from rfl,
    show L2362 ++ [F217] = L3025 from rfl] at h
  rw [i2044 hinj, i763 hinj] at h
  linarith

theorem row796 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2374 + (1 : ℝ) * HLm Γ 5 L3654 + (-1 : ℝ) * HLm Γ 5 L3656 + (-1 : ℝ) * HLm Γ 5 L187 := by
  have h := HLm_submod hΓ [F16] L187 [F228]
  rw [show [F16] ++ L187 ++ [F228] = L3657 from rfl, show [F16] ++ L187 = L3653 from rfl,
    show L187 ++ [F228] = L3655 from rfl] at h
  rw [i2047 hinj, i2045 hinj, i2046 hinj] at h
  linarith

theorem row797 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3658 + (1 : ℝ) * HLm Γ 5 L3056 + (-1 : ℝ) * HLm Γ 5 L3660 + (-1 : ℝ) * HLm Γ 5 L3054 := by
  have h := HLm_submod hΓ [F7] L3055 [F67]
  rw [show [F7] ++ L3055 ++ [F67] = L3661 from rfl, show [F7] ++ L3055 = L3659 from rfl,
    show L3055 ++ [F67] = L3057 from rfl] at h
  rw [i2049 hinj, i2048 hinj, i1738 hinj, i1737 hinj] at h
  linarith

theorem row798 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3662 + (1 : ℝ) * HLm Γ 5 L3146 + (-1 : ℝ) * HLm Γ 5 L3664 + (-1 : ℝ) * HLm Γ 5 L2841 := by
  have h := HLm_submod hΓ [F62] L2841 [F16]
  rw [show [F62] ++ L2841 ++ [F16] = L3665 from rfl, show [F62] ++ L2841 = L3663 from rfl,
    show L2841 ++ [F16] = L3147 from rfl] at h
  rw [i2051 hinj, i2050 hinj, i1784 hinj] at h
  linarith

theorem row799 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3146 + (1 : ℝ) * HLm Γ 5 L3667 + (-1 : ℝ) * HLm Γ 5 L3669 + (-1 : ℝ) * HLm Γ 5 L2841 := by
  have h := HLm_submod hΓ [F16] L2841 [F236]
  rw [show [F16] ++ L2841 ++ [F236] = L3670 from rfl, show [F16] ++ L2841 = L3666 from rfl,
    show L2841 ++ [F236] = L3668 from rfl] at h
  rw [i2054 hinj, i2052 hinj, i2053 hinj] at h
  linarith

theorem row800 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3671 + (1 : ℝ) * HLm Γ 5 L3673 + (-1 : ℝ) * HLm Γ 5 L3675 + (-1 : ℝ) * HLm Γ 5 L2918 := by
  have h := HLm_submod hΓ [F62] L2918 [F16]
  rw [show [F62] ++ L2918 ++ [F16] = L3676 from rfl, show [F62] ++ L2918 = L3672 from rfl,
    show L2918 ++ [F16] = L3674 from rfl] at h
  rw [i2057 hinj, i2055 hinj, i2056 hinj] at h
  linarith

theorem row801 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L258 + (1 : ℝ) * HLm Γ 5 L2931 + (-1 : ℝ) * HLm Γ 5 L3679 + (-1 : ℝ) * HLm Γ 5 L2929 := by
  have h := HLm_submod hΓ [F0] L3681 [F218]
  rw [show [F0] ++ L3681 ++ [F218] = L3680 from rfl, show [F0] ++ L3681 = L3677 from rfl,
    show L3681 ++ [F218] = L3678 from rfl] at h
  rw [i2060 hinj, i2058 hinj, i2059 hinj, i2061 hinj] at h
  linarith

theorem row802 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1480 + (1 : ℝ) * HLm Γ 5 L3030 + (-1 : ℝ) * HLm Γ 5 L3683 + (-1 : ℝ) * HLm Γ 5 L3026 := by
  have h := HLm_submod hΓ [F51] L3027 [F218]
  rw [show [F51] ++ L3027 ++ [F218] = L3684 from rfl, show [F51] ++ L3027 = L3682 from rfl,
    show L3027 ++ [F218] = L3031 from rfl] at h
  rw [i2063 hinj, i2062 hinj, i1723 hinj, i1721 hinj] at h
  linarith

theorem row803 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3685 + (1 : ℝ) * HLm Γ 5 L3687 + (-1 : ℝ) * HLm Γ 5 L3689 + (-1 : ℝ) * HLm Γ 5 L3691 := by
  have h := HLm_submod hΓ [F25] L3691 [F217]
  rw [show [F25] ++ L3691 ++ [F217] = L3690 from rfl, show [F25] ++ L3691 = L3686 from rfl,
    show L3691 ++ [F217] = L3688 from rfl] at h
  rw [i2066 hinj, i2064 hinj, i2065 hinj] at h
  linarith

theorem row804 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3692 + (1 : ℝ) * HLm Γ 5 L3694 + (-1 : ℝ) * HLm Γ 5 L3696 + (-1 : ℝ) * HLm Γ 5 L3698 := by
  have h := HLm_submod hΓ [F211] L3699 [F43]
  rw [show [F211] ++ L3699 ++ [F43] = L3697 from rfl, show [F211] ++ L3699 = L3693 from rfl,
    show L3699 ++ [F43] = L3695 from rfl] at h
  rw [i2069 hinj, i2067 hinj, i2068 hinj, i2070 hinj] at h
  linarith

theorem row805 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3700 + (1 : ℝ) * HLm Γ 5 L3702 + (-1 : ℝ) * HLm Γ 5 L3704 + (-1 : ℝ) * HLm Γ 5 L3706 := by
  have h := HLm_submod hΓ [F9] L3707 [F43]
  rw [show [F9] ++ L3707 ++ [F43] = L3705 from rfl, show [F9] ++ L3707 = L3701 from rfl,
    show L3707 ++ [F43] = L3703 from rfl] at h
  rw [i2073 hinj, i2071 hinj, i2072 hinj, i2074 hinj] at h
  linarith

theorem row806 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3708 + (1 : ℝ) * HLm Γ 5 L3710 + (-1 : ℝ) * HLm Γ 5 L3712 + (-1 : ℝ) * HLm Γ 5 L3032 := by
  have h := HLm_submod hΓ [F9] L3033 [F217]
  rw [show [F9] ++ L3033 ++ [F217] = L3713 from rfl, show [F9] ++ L3033 = L3709 from rfl,
    show L3033 ++ [F217] = L3711 from rfl] at h
  rw [i2077 hinj, i2075 hinj, i2076 hinj, i1724 hinj] at h
  linarith

theorem row807 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1027 + (1 : ℝ) * HLm Γ 5 L3715 + (-1 : ℝ) * HLm Γ 5 L3717 + (-1 : ℝ) * HLm Γ 5 L360 := by
  have h := HLm_submod hΓ [F22] L2093 [F23]
  rw [show [F22] ++ L2093 ++ [F23] = L3718 from rfl, show [F22] ++ L2093 = L3714 from rfl,
    show L2093 ++ [F23] = L3716 from rfl] at h
  rw [i2080 hinj, i2078 hinj, i2079 hinj, i1148 hinj] at h
  linarith

theorem row808 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3719 + (1 : ℝ) * HLm Γ 5 L3034 + (-1 : ℝ) * HLm Γ 5 L3722 + (-1 : ℝ) * HLm Γ 5 L3724 := by
  have h := HLm_submod hΓ [F16] L3724 [F25]
  rw [show [F16] ++ L3724 ++ [F25] = L3723 from rfl, show [F16] ++ L3724 = L3720 from rfl,
    show L3724 ++ [F25] = L3721 from rfl] at h
  rw [i2083 hinj, i2081 hinj, i2082 hinj] at h
  linarith

theorem row809 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3511 + (1 : ℝ) * HLm Γ 5 L3725 + (-1 : ℝ) * HLm Γ 5 L3727 + (-1 : ℝ) * HLm Γ 5 L2933 := by
  have h := HLm_submod hΓ [F9] L2934 [F236]
  rw [show [F9] ++ L2934 ++ [F236] = L3728 from rfl, show [F9] ++ L2934 = L3512 from rfl,
    show L2934 ++ [F236] = L3726 from rfl] at h
  rw [i2085 hinj, i1969 hinj, i2084 hinj, i1672 hinj] at h
  linarith

theorem row810 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2939 + (1 : ℝ) * HLm Γ 5 L3729 + (-1 : ℝ) * HLm Γ 5 L3731 + (-1 : ℝ) * HLm Γ 5 L2937 := by
  have h := HLm_submod hΓ [F0] L2938 [F16]
  rw [show [F0] ++ L2938 ++ [F16] = L3732 from rfl, show [F0] ++ L2938 = L2940 from rfl,
    show L2938 ++ [F16] = L3730 from rfl] at h
  rw [i2087 hinj, i1675 hinj, i2086 hinj, i1674 hinj] at h
  linarith

theorem row811 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3733 + (1 : ℝ) * HLm Γ 5 L3217 + (-1 : ℝ) * HLm Γ 5 L3735 + (-1 : ℝ) * HLm Γ 5 L3213 := by
  have h := HLm_submod hΓ [F1] L3214 [F85]
  rw [show [F1] ++ L3214 ++ [F85] = L3736 from rfl, show [F1] ++ L3214 = L3734 from rfl,
    show L3214 ++ [F85] = L3218 from rfl] at h
  rw [i2089 hinj, i2088 hinj, i1818 hinj, i1816 hinj] at h
  linarith

theorem row812 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3737 + (1 : ℝ) * HLm Γ 5 L2978 + (-1 : ℝ) * HLm Γ 5 L3739 + (-1 : ℝ) * HLm Γ 5 L2974 := by
  have h := HLm_submod hΓ [F86] L2975 [F218]
  rw [show [F86] ++ L2975 ++ [F218] = L3740 from rfl, show [F86] ++ L2975 = L3738 from rfl,
    show L2975 ++ [F218] = L2979 from rfl] at h
  rw [i2091 hinj, i2090 hinj, i1698 hinj, i1696 hinj] at h
  linarith

theorem row813 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2944 + (1 : ℝ) * HLm Γ 5 L3741 + (-1 : ℝ) * HLm Γ 5 L3743 + (-1 : ℝ) * HLm Γ 5 L2942 := by
  have h := HLm_submod hΓ [F67] L2943 [F211]
  rw [show [F67] ++ L2943 ++ [F211] = L3744 from rfl, show [F67] ++ L2943 = L2945 from rfl,
    show L2943 ++ [F211] = L3742 from rfl] at h
  rw [i2093 hinj, i1678 hinj, i2092 hinj, i1677 hinj] at h
  linarith

theorem row814 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3745 + (1 : ℝ) * HLm Γ 5 L3747 + (-1 : ℝ) * HLm Γ 5 L3749 + (-1 : ℝ) * HLm Γ 5 L3751 := by
  have h := HLm_submod hΓ [F1] L3752 [F67]
  rw [show [F1] ++ L3752 ++ [F67] = L3750 from rfl, show [F1] ++ L3752 = L3746 from rfl,
    show L3752 ++ [F67] = L3748 from rfl] at h
  rw [i2096 hinj, i2094 hinj, i2095 hinj, i2097 hinj] at h
  linarith

theorem row815 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3753 + (1 : ℝ) * HLm Γ 5 L3755 + (-1 : ℝ) * HLm Γ 5 L3757 + (-1 : ℝ) * HLm Γ 5 L910 := by
  have h := HLm_submod hΓ [F67] L911 [F228]
  rw [show [F67] ++ L911 ++ [F228] = L3758 from rfl, show [F67] ++ L911 = L3754 from rfl,
    show L911 ++ [F228] = L3756 from rfl] at h
  rw [i2100 hinj, i2098 hinj, i2099 hinj, i418 hinj] at h
  linarith

theorem row816 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3759 + (1 : ℝ) * HLm Γ 5 L3761 + (-1 : ℝ) * HLm Γ 5 L3763 + (-1 : ℝ) * HLm Γ 5 L3765 := by
  have h := HLm_submod hΓ [F62] L3766 [F27]
  rw [show [F62] ++ L3766 ++ [F27] = L3764 from rfl, show [F62] ++ L3766 = L3760 from rfl,
    show L3766 ++ [F27] = L3762 from rfl] at h
  rw [i2103 hinj, i2101 hinj, i2102 hinj, i2104 hinj] at h
  linarith

theorem row817 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L897 + (1 : ℝ) * HLm Γ 5 L2959 + (-1 : ℝ) * HLm Γ 5 L3769 + (-1 : ℝ) * HLm Γ 5 L2957 := by
  have h := HLm_submod hΓ [F7] L3771 [F217]
  rw [show [F7] ++ L3771 ++ [F217] = L3770 from rfl, show [F7] ++ L3771 = L3767 from rfl,
    show L3771 ++ [F217] = L3768 from rfl] at h
  rw [i2107 hinj, i2105 hinj, i2106 hinj, i2108 hinj] at h
  linarith

theorem row818 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2391 + (1 : ℝ) * HLm Γ 5 L3773 + (-1 : ℝ) * HLm Γ 5 L3775 + (-1 : ℝ) * HLm Γ 5 L2395 := by
  have h := HLm_submod hΓ [F16] L2395 [F211]
  rw [show [F16] ++ L2395 ++ [F211] = L3776 from rfl, show [F16] ++ L2395 = L3772 from rfl,
    show L2395 ++ [F211] = L3774 from rfl] at h
  rw [i2111 hinj, i2109 hinj, i2110 hinj] at h
  linarith

theorem row819 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L208 + (1 : ℝ) * HLm Γ 5 L3777 + (-1 : ℝ) * HLm Γ 5 L3779 + (-1 : ℝ) * HLm Γ 5 L206 := by
  have h := HLm_submod hΓ [F47] L207 [F228]
  rw [show [F47] ++ L207 ++ [F228] = L3780 from rfl, show [F47] ++ L207 = L209 from rfl,
    show L207 ++ [F228] = L3778 from rfl] at h
  rw [i2113 hinj, i73 hinj, i2112 hinj, i72 hinj] at h
  linarith

theorem row820 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3781 + (1 : ℝ) * HLm Γ 5 L3783 + (-1 : ℝ) * HLm Γ 5 L3785 + (-1 : ℝ) * HLm Γ 5 L2948 := by
  have h := HLm_submod hΓ [F47] L2949 [F16]
  rw [show [F47] ++ L2949 ++ [F16] = L3786 from rfl, show [F47] ++ L2949 = L3782 from rfl,
    show L2949 ++ [F16] = L3784 from rfl] at h
  rw [i2116 hinj, i2114 hinj, i2115 hinj, i1680 hinj] at h
  linarith

theorem row821 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L940 + (1 : ℝ) * HLm Γ 5 L3788 + (-1 : ℝ) * HLm Γ 5 L3790 + (-1 : ℝ) * HLm Γ 5 L1968 := by
  have h := HLm_submod hΓ [F2] L1969 [F217]
  rw [show [F2] ++ L1969 ++ [F217] = L3791 from rfl, show [F2] ++ L1969 = L3787 from rfl,
    show L1969 ++ [F217] = L3789 from rfl] at h
  rw [i2119 hinj, i2117 hinj, i2118 hinj, i1085 hinj] at h
  linarith

theorem row822 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3792 + (1 : ℝ) * HLm Γ 5 L3687 + (-1 : ℝ) * HLm Γ 5 L3795 + (-1 : ℝ) * HLm Γ 5 L3797 := by
  have h := HLm_submod hΓ [F9] L3798 [F3]
  rw [show [F9] ++ L3798 ++ [F3] = L3796 from rfl, show [F9] ++ L3798 = L3793 from rfl,
    show L3798 ++ [F3] = L3794 from rfl] at h
  rw [i2122 hinj, i2120 hinj, i2121 hinj, i2123 hinj] at h
  linarith

theorem row823 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2077 + (1 : ℝ) * HLm Γ 5 L2966 + (-1 : ℝ) * HLm Γ 5 L1348 + (-1 : ℝ) * HLm Γ 5 L2084 := by
  have h := HLm_submod hΓ [F0] L2084 [F67]
  rw [show [F0] ++ L2084 ++ [F67] = L3799 from rfl, show [F0] ++ L2084 = L2396 from rfl,
    show L2084 ++ [F67] = L2966 from rfl] at h
  rw [i2124 hinj, i1318 hinj] at h
  linarith

theorem row824 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3800 + (1 : ℝ) * HLm Γ 5 L3802 + (-1 : ℝ) * HLm Γ 5 L3804 + (-1 : ℝ) * HLm Γ 5 L3806 := by
  have h := HLm_submod hΓ [F7] L3807 [F6]
  rw [show [F7] ++ L3807 ++ [F6] = L3805 from rfl, show [F7] ++ L3807 = L3801 from rfl,
    show L3807 ++ [F6] = L3803 from rfl] at h
  rw [i2127 hinj, i2125 hinj, i2126 hinj, i2128 hinj] at h
  linarith

theorem row825 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3808 + (1 : ℝ) * HLm Γ 5 L3810 + (-1 : ℝ) * HLm Γ 5 L3812 + (-1 : ℝ) * HLm Γ 5 L3814 := by
  have h := HLm_submod hΓ [F25] L3815 [F219]
  rw [show [F25] ++ L3815 ++ [F219] = L3813 from rfl, show [F25] ++ L3815 = L3809 from rfl,
    show L3815 ++ [F219] = L3811 from rfl] at h
  rw [i2131 hinj, i2129 hinj, i2130 hinj, i2132 hinj] at h
  linarith

theorem row826 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3816 + (1 : ℝ) * HLm Γ 5 L3818 + (-1 : ℝ) * HLm Γ 5 L3820 + (-1 : ℝ) * HLm Γ 5 L3822 := by
  have h := HLm_submod hΓ [F82] L3822 [F211]
  rw [show [F82] ++ L3822 ++ [F211] = L3821 from rfl, show [F82] ++ L3822 = L3817 from rfl,
    show L3822 ++ [F211] = L3819 from rfl] at h
  rw [i2135 hinj, i2133 hinj, i2134 hinj] at h
  linarith

theorem row827 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3823 + (1 : ℝ) * HLm Γ 5 L3825 + (-1 : ℝ) * HLm Γ 5 L3827 + (-1 : ℝ) * HLm Γ 5 L3829 := by
  have h := HLm_submod hΓ [F3] L3830 [F68]
  rw [show [F3] ++ L3830 ++ [F68] = L3828 from rfl, show [F3] ++ L3830 = L3824 from rfl,
    show L3830 ++ [F68] = L3826 from rfl] at h
  rw [i2138 hinj, i2136 hinj, i2137 hinj, i2139 hinj] at h
  linarith

theorem row828 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3305 + (1 : ℝ) * HLm Γ 5 L3211 + (-1 : ℝ) * HLm Γ 5 L3307 + (-1 : ℝ) * HLm Γ 5 L3209 := by
  have h := HLm_submod hΓ [F1] L3209 [F7]
  rw [show [F1] ++ L3209 ++ [F7] = L3833 from rfl, show [F1] ++ L3209 = L3831 from rfl,
    show L3209 ++ [F7] = L3832 from rfl] at h
  rw [i2142 hinj, i2140 hinj, i2141 hinj] at h
  linarith

theorem row829 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3834 + (1 : ℝ) * HLm Γ 5 L3836 + (-1 : ℝ) * HLm Γ 5 L3838 + (-1 : ℝ) * HLm Γ 5 L1009 := by
  have h := HLm_submod hΓ [F52] L1010 [F228]
  rw [show [F52] ++ L1010 ++ [F228] = L3839 from rfl, show [F52] ++ L1010 = L3835 from rfl,
    show L1010 ++ [F228] = L3837 from rfl] at h
  rw [i2145 hinj, i2143 hinj, i2144 hinj, i470 hinj] at h
  linarith

theorem row830 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L245 + (1 : ℝ) * HLm Γ 5 L3840 + (-1 : ℝ) * HLm Γ 5 L3842 + (-1 : ℝ) * HLm Γ 5 L243 := by
  have h := HLm_submod hΓ [F67] L244 [F214]
  rw [show [F67] ++ L244 ++ [F214] = L3843 from rfl, show [F67] ++ L244 = L246 from rfl,
    show L244 ++ [F214] = L3841 from rfl] at h
  rw [i2147 hinj, i89 hinj, i2146 hinj, i88 hinj] at h
  linarith

theorem row831 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3844 + (1 : ℝ) * HLm Γ 5 L3846 + (-1 : ℝ) * HLm Γ 5 L3848 + (-1 : ℝ) * HLm Γ 5 L457 := by
  have h := HLm_submod hΓ [F228] L3850 [F43]
  rw [show [F228] ++ L3850 ++ [F43] = L3849 from rfl, show [F228] ++ L3850 = L3845 from rfl,
    show L3850 ++ [F43] = L3847 from rfl] at h
  rw [i2150 hinj, i2148 hinj, i2149 hinj, i2151 hinj] at h
  linarith

theorem row832 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3851 + (1 : ℝ) * HLm Γ 5 L3853 + (-1 : ℝ) * HLm Γ 5 L3855 + (-1 : ℝ) * HLm Γ 5 L3857 := by
  have h := HLm_submod hΓ [F0] L3858 [F43]
  rw [show [F0] ++ L3858 ++ [F43] = L3856 from rfl, show [F0] ++ L3858 = L3852 from rfl,
    show L3858 ++ [F43] = L3854 from rfl] at h
  rw [i2154 hinj, i2152 hinj, i2153 hinj, i2155 hinj] at h
  linarith

theorem row833 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3859 + (1 : ℝ) * HLm Γ 5 L3861 + (-1 : ℝ) * HLm Γ 5 L3863 + (-1 : ℝ) * HLm Γ 5 L3865 := by
  have h := HLm_submod hΓ [F2] L3866 [F218]
  rw [show [F2] ++ L3866 ++ [F218] = L3864 from rfl, show [F2] ++ L3866 = L3860 from rfl,
    show L3866 ++ [F218] = L3862 from rfl] at h
  rw [i2158 hinj, i2156 hinj, i2157 hinj, i2159 hinj] at h
  linarith

theorem row834 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3867 + (1 : ℝ) * HLm Γ 5 L3869 + (-1 : ℝ) * HLm Γ 5 L3871 + (-1 : ℝ) * HLm Γ 5 L3865 := by
  have h := HLm_submod hΓ [F228] L3866 [F45]
  rw [show [F228] ++ L3866 ++ [F45] = L3872 from rfl, show [F228] ++ L3866 = L3868 from rfl,
    show L3866 ++ [F45] = L3870 from rfl] at h
  rw [i2162 hinj, i2160 hinj, i2161 hinj, i2159 hinj] at h
  linarith

theorem row835 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3873 + (1 : ℝ) * HLm Γ 5 L3875 + (-1 : ℝ) * HLm Γ 5 L3877 + (-1 : ℝ) * HLm Γ 5 L3879 := by
  have h := HLm_submod hΓ [F9] L3880 [F55]
  rw [show [F9] ++ L3880 ++ [F55] = L3878 from rfl, show [F9] ++ L3880 = L3874 from rfl,
    show L3880 ++ [F55] = L3876 from rfl] at h
  rw [i2165 hinj, i2163 hinj, i2164 hinj, i2166 hinj] at h
  linarith

theorem row836 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L330 + (1 : ℝ) * HLm Γ 5 L2983 + (-1 : ℝ) * HLm Γ 5 L3883 + (-1 : ℝ) * HLm Γ 5 L329 := by
  have h := HLm_submod hΓ [F0] L2982 [F210]
  rw [show [F0] ++ L2982 ++ [F210] = L3884 from rfl, show [F0] ++ L2982 = L3881 from rfl,
    show L2982 ++ [F210] = L3882 from rfl] at h
  rw [i2169 hinj, i2167 hinj, i2168 hinj, i1700 hinj] at h
  linarith

theorem row837 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3087 + (1 : ℝ) * HLm Γ 5 L3094 + (-1 : ℝ) * HLm Γ 5 L3886 + (-1 : ℝ) * HLm Γ 5 L384 := by
  have h := HLm_submod hΓ [F0] L2989 [F210]
  rw [show [F0] ++ L2989 ++ [F210] = L3887 from rfl, show [F0] ++ L2989 = L3885 from rfl,
    show L2989 ++ [F210] = L3095 from rfl] at h
  rw [i2171 hinj, i2170 hinj, i1757 hinj, i1704 hinj] at h
  linarith

theorem row838 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L883 + (1 : ℝ) * HLm Γ 5 L3134 + (-1 : ℝ) * HLm Γ 5 L3889 + (-1 : ℝ) * HLm Γ 5 L417 := by
  have h := HLm_submod hΓ [F12] L3132 [F210]
  rw [show [F12] ++ L3132 ++ [F210] = L3890 from rfl, show [F12] ++ L3132 = L3888 from rfl,
    show L3132 ++ [F210] = L3135 from rfl] at h
  rw [i2173 hinj, i2172 hinj, i1777 hinj, i1776 hinj] at h
  linarith

theorem row839 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3891 + (1 : ℝ) * HLm Γ 5 L3893 + (-1 : ℝ) * HLm Γ 5 L3895 + (-1 : ℝ) * HLm Γ 5 L2141 := by
  have h := HLm_submod hΓ [F3] L2142 [F228]
  rw [show [F3] ++ L2142 ++ [F228] = L3896 from rfl, show [F3] ++ L2142 = L3892 from rfl,
    show L2142 ++ [F228] = L3894 from rfl] at h
  rw [i2176 hinj, i2174 hinj, i2175 hinj, i1174 hinj] at h
  linarith

theorem row840 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3897 + (1 : ℝ) * HLm Γ 5 L3899 + (-1 : ℝ) * HLm Γ 5 L3901 + (-1 : ℝ) * HLm Γ 5 L3903 := by
  have h := HLm_submod hΓ [F1] L3903 [F27]
  rw [show [F1] ++ L3903 ++ [F27] = L3902 from rfl, show [F1] ++ L3903 = L3898 from rfl,
    show L3903 ++ [F27] = L3900 from rfl] at h
  rw [i2179 hinj, i2177 hinj, i2178 hinj] at h
  linarith

theorem row841 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3904 + (1 : ℝ) * HLm Γ 5 L3023 + (-1 : ℝ) * HLm Γ 5 L3906 + (-1 : ℝ) * HLm Γ 5 L3021 := by
  have h := HLm_submod hΓ [F211] L3022 [F90]
  rw [show [F211] ++ L3022 ++ [F90] = L3907 from rfl, show [F211] ++ L3022 = L3905 from rfl,
    show L3022 ++ [F90] = L3024 from rfl] at h
  rw [i2181 hinj, i2180 hinj, i1720 hinj, i1719 hinj] at h
  linarith

theorem row842 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3908 + (1 : ℝ) * HLm Γ 5 L2996 + (-1 : ℝ) * HLm Γ 5 L3911 + (-1 : ℝ) * HLm Γ 5 L2994 := by
  have h := HLm_submod hΓ [F5] L2995 [F228]
  rw [show [F5] ++ L2995 ++ [F228] = L3912 from rfl, show [F5] ++ L2995 = L3909 from rfl,
    show L2995 ++ [F228] = L3910 from rfl] at h
  rw [i2184 hinj, i2182 hinj, i2183 hinj, i1707 hinj] at h
  linarith

theorem row843 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3087 + (1 : ℝ) * HLm Γ 5 L3102 + (-1 : ℝ) * HLm Γ 5 L3914 + (-1 : ℝ) * HLm Γ 5 L3100 := by
  have h := HLm_submod hΓ [F0] L3100 [F236]
  rw [show [F0] ++ L3100 ++ [F236] = L3915 from rfl, show [F0] ++ L3100 = L3913 from rfl,
    show L3100 ++ [F236] = L3102 from rfl] at h
  rw [i2186 hinj, i2185 hinj] at h
  linarith

theorem row844 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3916 + (1 : ℝ) * HLm Γ 5 L3918 + (-1 : ℝ) * HLm Γ 5 L3920 + (-1 : ℝ) * HLm Γ 5 L3100 := by
  have h := HLm_submod hΓ [F3] L3100 [F211]
  rw [show [F3] ++ L3100 ++ [F211] = L3921 from rfl, show [F3] ++ L3100 = L3917 from rfl,
    show L3100 ++ [F211] = L3919 from rfl] at h
  rw [i2189 hinj, i2187 hinj, i2188 hinj] at h
  linarith

theorem row845 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2210 + (1 : ℝ) * HLm Γ 5 L3128 + (-1 : ℝ) * HLm Γ 5 L3923 + (-1 : ℝ) * HLm Γ 5 L400 := by
  have h := HLm_submod hΓ [F0] L400 [F214]
  rw [show [F0] ++ L400 ++ [F214] = L3924 from rfl, show [F0] ++ L400 = L3922 from rfl,
    show L400 ++ [F214] = L3129 from rfl] at h
  rw [i2191 hinj, i2190 hinj, i1773 hinj] at h
  linarith

theorem row846 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3925 + (1 : ℝ) * HLm Γ 5 L3927 + (-1 : ℝ) * HLm Γ 5 L3929 + (-1 : ℝ) * HLm Γ 5 L2147 := by
  have h := HLm_submod hΓ [F214] L2148 [F27]
  rw [show [F214] ++ L2148 ++ [F27] = L3930 from rfl, show [F214] ++ L2148 = L3926 from rfl,
    show L2148 ++ [F27] = L3928 from rfl] at h
  rw [i2194 hinj, i2192 hinj, i2193 hinj, i1177 hinj] at h
  linarith

theorem row847 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3931 + (1 : ℝ) * HLm Γ 5 L3933 + (-1 : ℝ) * HLm Γ 5 L3935 + (-1 : ℝ) * HLm Γ 5 L3937 := by
  have h := HLm_submod hΓ [F2] L3938 [F211]
  rw [show [F2] ++ L3938 ++ [F211] = L3936 from rfl, show [F2] ++ L3938 = L3932 from rfl,
    show L3938 ++ [F211] = L3934 from rfl] at h
  rw [i2197 hinj, i2195 hinj, i2196 hinj, i2198 hinj] at h
  linarith

theorem row848 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3939 + (1 : ℝ) * HLm Γ 5 L3941 + (-1 : ℝ) * HLm Γ 5 L3943 + (-1 : ℝ) * HLm Γ 5 L3945 := by
  have h := HLm_submod hΓ [F1] L3945 [F27]
  rw [show [F1] ++ L3945 ++ [F27] = L3944 from rfl, show [F1] ++ L3945 = L3940 from rfl,
    show L3945 ++ [F27] = L3942 from rfl] at h
  rw [i2201 hinj, i2199 hinj, i2200 hinj] at h
  linarith

theorem row849 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L310 + (1 : ℝ) * HLm Γ 5 L3947 + (-1 : ℝ) * HLm Γ 5 L3949 + (-1 : ℝ) * HLm Γ 5 L309 := by
  have h := HLm_submod hΓ [F9] L3951 [F3]
  rw [show [F9] ++ L3951 ++ [F3] = L3950 from rfl, show [F9] ++ L3951 = L3946 from rfl,
    show L3951 ++ [F3] = L3948 from rfl] at h
  rw [i2204 hinj, i2202 hinj, i2203 hinj, i2205 hinj] at h
  linarith

theorem row850 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3952 + (1 : ℝ) * HLm Γ 5 L3954 + (-1 : ℝ) * HLm Γ 5 L3956 + (-1 : ℝ) * HLm Γ 5 L309 := by
  have h := HLm_submod hΓ [F210] L3951 [F6]
  rw [show [F210] ++ L3951 ++ [F6] = L3957 from rfl, show [F210] ++ L3951 = L3953 from rfl,
    show L3951 ++ [F6] = L3955 from rfl] at h
  rw [i2208 hinj, i2206 hinj, i2207 hinj, i2205 hinj] at h
  linarith

theorem row851 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3958 + (1 : ℝ) * HLm Γ 5 L3960 + (-1 : ℝ) * HLm Γ 5 L3962 + (-1 : ℝ) * HLm Γ 5 L2102 := by
  have h := HLm_submod hΓ [F210] L3964 [F33]
  rw [show [F210] ++ L3964 ++ [F33] = L3963 from rfl, show [F210] ++ L3964 = L3959 from rfl,
    show L3964 ++ [F33] = L3961 from rfl] at h
  rw [i2211 hinj, i2209 hinj, i2210 hinj, i2212 hinj] at h
  linarith

theorem row852 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1135 + (1 : ℝ) * HLm Γ 5 L3123 + (-1 : ℝ) * HLm Γ 5 L3966 + (-1 : ℝ) * HLm Γ 5 L3120 := by
  have h := HLm_submod hΓ [F1] L3121 [F228]
  rw [show [F1] ++ L3121 ++ [F228] = L3967 from rfl, show [F1] ++ L3121 = L3965 from rfl,
    show L3121 ++ [F228] = L3124 from rfl] at h
  rw [i2214 hinj, i2213 hinj, i1771 hinj, i1770 hinj] at h
  linarith

theorem row853 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3968 + (1 : ℝ) * HLm Γ 5 L3970 + (-1 : ℝ) * HLm Γ 5 L3972 + (-1 : ℝ) * HLm Γ 5 L3974 := by
  have h := HLm_submod hΓ [F3] L3975 [F45]
  rw [show [F3] ++ L3975 ++ [F45] = L3973 from rfl, show [F3] ++ L3975 = L3969 from rfl,
    show L3975 ++ [F45] = L3971 from rfl] at h
  rw [i2217 hinj, i2215 hinj, i2216 hinj, i2218 hinj] at h
  linarith

theorem row854 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3976 + (1 : ℝ) * HLm Γ 5 L3978 + (-1 : ℝ) * HLm Γ 5 L3980 + (-1 : ℝ) * HLm Γ 5 L423 := by
  have h := HLm_submod hΓ [F2] L3982 [F228]
  rw [show [F2] ++ L3982 ++ [F228] = L3981 from rfl, show [F2] ++ L3982 = L3977 from rfl,
    show L3982 ++ [F228] = L3979 from rfl] at h
  rw [i2221 hinj, i2219 hinj, i2220 hinj, i2222 hinj] at h
  linarith

theorem row855 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3983 + (1 : ℝ) * HLm Γ 5 L3985 + (-1 : ℝ) * HLm Γ 5 L3987 + (-1 : ℝ) * HLm Γ 5 L3001 := by
  have h := HLm_submod hΓ [F1] L3002 [F228]
  rw [show [F1] ++ L3002 ++ [F228] = L3988 from rfl, show [F1] ++ L3002 = L3984 from rfl,
    show L3002 ++ [F228] = L3986 from rfl] at h
  rw [i2225 hinj, i2223 hinj, i2224 hinj, i1710 hinj] at h
  linarith

theorem row856 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3989 + (1 : ℝ) * HLm Γ 5 L3007 + (-1 : ℝ) * HLm Γ 5 L3992 + (-1 : ℝ) * HLm Γ 5 L3005 := by
  have h := HLm_submod hΓ [F2] L3994 [F86]
  rw [show [F2] ++ L3994 ++ [F86] = L3993 from rfl, show [F2] ++ L3994 = L3990 from rfl,
    show L3994 ++ [F86] = L3991 from rfl] at h
  rw [i2228 hinj, i2226 hinj, i2227 hinj, i2229 hinj] at h
  linarith

theorem row857 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3995 + (1 : ℝ) * HLm Γ 5 L3997 + (-1 : ℝ) * HLm Γ 5 L3999 + (-1 : ℝ) * HLm Γ 5 L2085 := by
  have h := HLm_submod hΓ [F214] L4001 [F55]
  rw [show [F214] ++ L4001 ++ [F55] = L4000 from rfl, show [F214] ++ L4001 = L3996 from rfl,
    show L4001 ++ [F55] = L3998 from rfl] at h
  rw [i2232 hinj, i2230 hinj, i2231 hinj, i2233 hinj] at h
  linarith

theorem row858 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2904 + (1 : ℝ) * HLm Γ 5 L4003 + (-1 : ℝ) * HLm Γ 5 L4005 + (-1 : ℝ) * HLm Γ 5 L294 := by
  have h := HLm_submod hΓ [F9] L3047 [F214]
  rw [show [F9] ++ L3047 ++ [F214] = L4006 from rfl, show [F9] ++ L3047 = L4002 from rfl,
    show L3047 ++ [F214] = L4004 from rfl] at h
  rw [i2236 hinj, i2234 hinj, i2235 hinj, i1733 hinj] at h
  linarith

theorem row859 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4007 + (1 : ℝ) * HLm Γ 5 L3048 + (-1 : ℝ) * HLm Γ 5 L4009 + (-1 : ℝ) * HLm Γ 5 L294 := by
  have h := HLm_submod hΓ [F3] L3047 [F85]
  rw [show [F3] ++ L3047 ++ [F85] = L4010 from rfl, show [F3] ++ L3047 = L4008 from rfl,
    show L3047 ++ [F85] = L3049 from rfl] at h
  rw [i2238 hinj, i2237 hinj, i1734 hinj, i1733 hinj] at h
  linarith

theorem row860 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3063 + (1 : ℝ) * HLm Γ 5 L4012 + (-1 : ℝ) * HLm Γ 5 L4014 + (-1 : ℝ) * HLm Γ 5 L2855 := by
  have h := HLm_submod hΓ [F22] L2856 [F210]
  rw [show [F22] ++ L2856 ++ [F210] = L4015 from rfl, show [F22] ++ L2856 = L4011 from rfl,
    show L2856 ++ [F210] = L4013 from rfl] at h
  rw [i2241 hinj, i2239 hinj, i2240 hinj, i1635 hinj] at h
  linarith

theorem row861 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4016 + (1 : ℝ) * HLm Γ 5 L4018 + (-1 : ℝ) * HLm Γ 5 L4020 + (-1 : ℝ) * HLm Γ 5 L4022 := by
  have h := HLm_submod hΓ [F47] L4023 [F210]
  rw [show [F47] ++ L4023 ++ [F210] = L4021 from rfl, show [F47] ++ L4023 = L4017 from rfl,
    show L4023 ++ [F210] = L4019 from rfl] at h
  rw [i2244 hinj, i2242 hinj, i2243 hinj, i2245 hinj] at h
  linarith

theorem row862 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4024 + (1 : ℝ) * HLm Γ 5 L4026 + (-1 : ℝ) * HLm Γ 5 L4028 + (-1 : ℝ) * HLm Γ 5 L4030 := by
  have h := HLm_submod hΓ [F9] L4031 [F219]
  rw [show [F9] ++ L4031 ++ [F219] = L4029 from rfl, show [F9] ++ L4031 = L4025 from rfl,
    show L4031 ++ [F219] = L4027 from rfl] at h
  rw [i2248 hinj, i2246 hinj, i2247 hinj, i2249 hinj] at h
  linarith

theorem row863 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4032 + (1 : ℝ) * HLm Γ 5 L4034 + (-1 : ℝ) * HLm Γ 5 L4036 + (-1 : ℝ) * HLm Γ 5 L4038 := by
  have h := HLm_submod hΓ [F9] L4039 [F6]
  rw [show [F9] ++ L4039 ++ [F6] = L4037 from rfl, show [F9] ++ L4039 = L4033 from rfl,
    show L4039 ++ [F6] = L4035 from rfl] at h
  rw [i2252 hinj, i2250 hinj, i2251 hinj, i2253 hinj] at h
  linarith

theorem row864 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3167 + (1 : ℝ) * HLm Γ 5 L4041 + (-1 : ℝ) * HLm Γ 5 L4043 + (-1 : ℝ) * HLm Γ 5 L3165 := by
  have h := HLm_submod hΓ [F2] L3165 [F9]
  rw [show [F2] ++ L3165 ++ [F9] = L4044 from rfl, show [F2] ++ L3165 = L4040 from rfl,
    show L3165 ++ [F9] = L4042 from rfl] at h
  rw [i2256 hinj, i2254 hinj, i2255 hinj] at h
  linarith

theorem row865 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4045 + (1 : ℝ) * HLm Γ 5 L3189 + (-1 : ℝ) * HLm Γ 5 L4048 + (-1 : ℝ) * HLm Γ 5 L3011 := by
  have h := HLm_submod hΓ [F0] L3011 [F16]
  rw [show [F0] ++ L3011 ++ [F16] = L4049 from rfl, show [F0] ++ L3011 = L4046 from rfl,
    show L3011 ++ [F16] = L4047 from rfl] at h
  rw [i2259 hinj, i2257 hinj, i2258 hinj] at h
  linarith

theorem row866 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4050 + (1 : ℝ) * HLm Γ 5 L3202 + (-1 : ℝ) * HLm Γ 5 L4053 + (-1 : ℝ) * HLm Γ 5 L4055 := by
  have h := HLm_submod hΓ [F9] L4056 [F6]
  rw [show [F9] ++ L4056 ++ [F6] = L4054 from rfl, show [F9] ++ L4056 = L4051 from rfl,
    show L4056 ++ [F6] = L4052 from rfl] at h
  rw [i2262 hinj, i2260 hinj, i2261 hinj, i2263 hinj] at h
  linarith

theorem row867 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3388 + (1 : ℝ) * HLm Γ 5 L4058 + (-1 : ℝ) * HLm Γ 5 L4059 + (-1 : ℝ) * HLm Γ 5 L4061 := by
  have h := HLm_submod hΓ [F7] L4061 [F2]
  rw [show [F7] ++ L4061 ++ [F2] = L4060 from rfl, show [F7] ++ L4061 = L4057 from rfl,
    show L4061 ++ [F2] = L4058 from rfl] at h
  rw [i2265 hinj, i2264 hinj] at h
  linarith

theorem row868 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4058 + (1 : ℝ) * HLm Γ 5 L3598 + (-1 : ℝ) * HLm Γ 5 L3600 + (-1 : ℝ) * HLm Γ 5 L4061 := by
  have h := HLm_submod hΓ [F2] L4061 [F9]
  rw [show [F2] ++ L4061 ++ [F9] = L4064 from rfl, show [F2] ++ L4061 = L4062 from rfl,
    show L4061 ++ [F9] = L4063 from rfl] at h
  rw [i2268 hinj, i2266 hinj, i2267 hinj] at h
  linarith

theorem row869 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4065 + (1 : ℝ) * HLm Γ 5 L4066 + (-1 : ℝ) * HLm Γ 5 L4068 + (-1 : ℝ) * HLm Γ 5 L3199 := by
  have h := HLm_submod hΓ [F0] L3199 [F2]
  rw [show [F0] ++ L3199 ++ [F2] = L4069 from rfl, show [F0] ++ L3199 = L4065 from rfl,
    show L3199 ++ [F2] = L4067 from rfl] at h
  rw [i2270 hinj, i2269 hinj] at h
  linarith

theorem row870 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4070 + (1 : ℝ) * HLm Γ 5 L4072 + (-1 : ℝ) * HLm Γ 5 L4074 + (-1 : ℝ) * HLm Γ 5 L4076 := by
  have h := HLm_submod hΓ [F9] L4077 [F219]
  rw [show [F9] ++ L4077 ++ [F219] = L4075 from rfl, show [F9] ++ L4077 = L4071 from rfl,
    show L4077 ++ [F219] = L4073 from rfl] at h
  rw [i2273 hinj, i2271 hinj, i2272 hinj, i2274 hinj] at h
  linarith

theorem row871 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1011 + (1 : ℝ) * HLm Γ 5 L4079 + (-1 : ℝ) * HLm Γ 5 L4081 + (-1 : ℝ) * HLm Γ 5 L3017 := by
  have h := HLm_submod hΓ [F2] L3018 [F218]
  rw [show [F2] ++ L3018 ++ [F218] = L4082 from rfl, show [F2] ++ L3018 = L4078 from rfl,
    show L3018 ++ [F218] = L4080 from rfl] at h
  rw [i2277 hinj, i2275 hinj, i2276 hinj, i1717 hinj] at h
  linarith

theorem row872 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4083 + (1 : ℝ) * HLm Γ 5 L4085 + (-1 : ℝ) * HLm Γ 5 L4087 + (-1 : ℝ) * HLm Γ 5 L3017 := by
  have h := HLm_submod hΓ [F210] L3018 [F6]
  rw [show [F210] ++ L3018 ++ [F6] = L4088 from rfl, show [F210] ++ L3018 = L4084 from rfl,
    show L3018 ++ [F6] = L4086 from rfl] at h
  rw [i2280 hinj, i2278 hinj, i2279 hinj, i1717 hinj] at h
  linarith

theorem row873 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L449 + (1 : ℝ) * HLm Γ 5 L4090 + (-1 : ℝ) * HLm Γ 5 L4092 + (-1 : ℝ) * HLm Γ 5 L1085 := by
  have h := HLm_submod hΓ [F85] L1086 [F217]
  rw [show [F85] ++ L1086 ++ [F217] = L4093 from rfl, show [F85] ++ L1086 = L4089 from rfl,
    show L1086 ++ [F217] = L4091 from rfl] at h
  rw [i2283 hinj, i2281 hinj, i2282 hinj, i513 hinj] at h
  linarith

theorem row874 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2950 + (1 : ℝ) * HLm Γ 5 L4095 + (-1 : ℝ) * HLm Γ 5 L4097 + (-1 : ℝ) * HLm Γ 5 L3028 := by
  have h := HLm_submod hΓ [F1] L3029 [F16]
  rw [show [F1] ++ L3029 ++ [F16] = L4098 from rfl, show [F1] ++ L3029 = L4094 from rfl,
    show L3029 ++ [F16] = L4096 from rfl] at h
  rw [i2286 hinj, i2284 hinj, i2285 hinj, i1722 hinj] at h
  linarith

theorem row875 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4099 + (1 : ℝ) * HLm Γ 5 L3927 + (-1 : ℝ) * HLm Γ 5 L4102 + (-1 : ℝ) * HLm Γ 5 L323 := by
  have h := HLm_submod hΓ [F3] L1101 [F52]
  rw [show [F3] ++ L1101 ++ [F52] = L4103 from rfl, show [F3] ++ L1101 = L4100 from rfl,
    show L1101 ++ [F52] = L4101 from rfl] at h
  rw [i2289 hinj, i2287 hinj, i2288 hinj, i521 hinj] at h
  linarith

theorem row876 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4104 + (1 : ℝ) * HLm Γ 5 L4106 + (-1 : ℝ) * HLm Γ 5 L4108 + (-1 : ℝ) * HLm Γ 5 L3043 := by
  have h := HLm_submod hΓ [F2] L3044 [F85]
  rw [show [F2] ++ L3044 ++ [F85] = L4109 from rfl, show [F2] ++ L3044 = L4105 from rfl,
    show L3044 ++ [F85] = L4107 from rfl] at h
  rw [i2292 hinj, i2290 hinj, i2291 hinj, i1731 hinj] at h
  linarith

theorem row877 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4110 + (1 : ℝ) * HLm Γ 5 L4112 + (-1 : ℝ) * HLm Γ 5 L4114 + (-1 : ℝ) * HLm Γ 5 L3090 := by
  have h := HLm_submod hΓ [F210] L3090 [F6]
  rw [show [F210] ++ L3090 ++ [F6] = L4115 from rfl, show [F210] ++ L3090 = L4111 from rfl,
    show L3090 ++ [F6] = L4113 from rfl] at h
  rw [i2295 hinj, i2293 hinj, i2294 hinj] at h
  linarith

theorem row878 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3118 + (1 : ℝ) * HLm Γ 5 L4117 + (-1 : ℝ) * HLm Γ 5 L4119 + (-1 : ℝ) * HLm Γ 5 L3116 := by
  have h := HLm_submod hΓ [F67] L4121 [F210]
  rw [show [F67] ++ L4121 ++ [F210] = L4120 from rfl, show [F67] ++ L4121 = L4116 from rfl,
    show L4121 ++ [F210] = L4118 from rfl] at h
  rw [i2298 hinj, i2296 hinj, i2297 hinj, i2299 hinj] at h
  linarith

theorem row879 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L918 + (1 : ℝ) * HLm Γ 5 L3138 + (-1 : ℝ) * HLm Γ 5 L4124 + (-1 : ℝ) * HLm Γ 5 L3136 := by
  have h := HLm_submod hΓ [F62] L4126 [F67]
  rw [show [F62] ++ L4126 ++ [F67] = L4125 from rfl, show [F62] ++ L4126 = L4122 from rfl,
    show L4126 ++ [F67] = L4123 from rfl] at h
  rw [i2302 hinj, i2300 hinj, i2301 hinj, i2303 hinj] at h
  linarith

theorem row880 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4127 + (1 : ℝ) * HLm Γ 5 L3157 + (-1 : ℝ) * HLm Γ 5 L4130 + (-1 : ℝ) * HLm Γ 5 L3155 := by
  have h := HLm_submod hΓ [F3] L4132 [F228]
  rw [show [F3] ++ L4132 ++ [F228] = L4131 from rfl, show [F3] ++ L4132 = L4128 from rfl,
    show L4132 ++ [F228] = L4129 from rfl] at h
  rw [i2306 hinj, i2304 hinj, i2305 hinj, i2307 hinj] at h
  linarith

theorem row881 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4133 + (1 : ℝ) * HLm Γ 5 L3069 + (-1 : ℝ) * HLm Γ 5 L4136 + (-1 : ℝ) * HLm Γ 5 L3067 := by
  have h := HLm_submod hΓ [F62] L3068 [F210]
  rw [show [F62] ++ L3068 ++ [F210] = L4137 from rfl, show [F62] ++ L3068 = L4134 from rfl,
    show L3068 ++ [F210] = L4135 from rfl] at h
  rw [i2310 hinj, i2308 hinj, i2309 hinj, i1745 hinj] at h
  linarith

theorem row882 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4138 + (1 : ℝ) * HLm Γ 5 L3197 + (-1 : ℝ) * HLm Γ 5 L4140 + (-1 : ℝ) * HLm Γ 5 L3073 := by
  have h := HLm_submod hΓ [F4] L3073 [F210]
  rw [show [F4] ++ L3073 ++ [F210] = L4141 from rfl, show [F4] ++ L3073 = L4139 from rfl,
    show L3073 ++ [F210] = L3197 from rfl] at h
  rw [i2312 hinj, i2311 hinj] at h
  linarith

theorem row883 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4142 + (1 : ℝ) * HLm Γ 5 L3197 + (-1 : ℝ) * HLm Γ 5 L4144 + (-1 : ℝ) * HLm Γ 5 L3073 := by
  have h := HLm_submod hΓ [F5] L3073 [F210]
  rw [show [F5] ++ L3073 ++ [F210] = L4145 from rfl, show [F5] ++ L3073 = L4143 from rfl,
    show L3073 ++ [F210] = L3197 from rfl] at h
  rw [i2314 hinj, i2313 hinj] at h
  linarith

theorem row884 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4142 + (1 : ℝ) * HLm Γ 5 L3074 + (-1 : ℝ) * HLm Γ 5 L4147 + (-1 : ℝ) * HLm Γ 5 L3073 := by
  have h := HLm_submod hΓ [F5] L3073 [F228]
  rw [show [F5] ++ L3073 ++ [F228] = L4148 from rfl, show [F5] ++ L3073 = L4143 from rfl,
    show L3073 ++ [F228] = L4146 from rfl] at h
  rw [i2316 hinj, i2313 hinj, i2315 hinj] at h
  linarith

theorem row885 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4149 + (1 : ℝ) * HLm Γ 5 L3084 + (-1 : ℝ) * HLm Γ 5 L4151 + (-1 : ℝ) * HLm Γ 5 L3083 := by
  have h := HLm_submod hΓ [F7] L3083 [F67]
  rw [show [F7] ++ L3083 ++ [F67] = L4152 from rfl, show [F7] ++ L3083 = L4150 from rfl,
    show L3083 ++ [F67] = L3084 from rfl] at h
  rw [i2318 hinj, i2317 hinj] at h
  linarith

theorem row886 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4153 + (1 : ℝ) * HLm Γ 5 L3177 + (-1 : ℝ) * HLm Γ 5 L4155 + (-1 : ℝ) * HLm Γ 5 L3175 := by
  have h := HLm_submod hΓ [F12] L3175 [F210]
  rw [show [F12] ++ L3175 ++ [F210] = L4156 from rfl, show [F12] ++ L3175 = L4154 from rfl,
    show L3175 ++ [F210] = L3177 from rfl] at h
  rw [i2320 hinj, i2319 hinj] at h
  linarith

theorem row887 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3592 + (1 : ℝ) * HLm Γ 5 L3152 + (-1 : ℝ) * HLm Γ 5 L4159 + (-1 : ℝ) * HLm Γ 5 L3150 := by
  have h := HLm_submod hΓ [F9] L4161 [F210]
  rw [show [F9] ++ L4161 ++ [F210] = L4160 from rfl, show [F9] ++ L4161 = L4157 from rfl,
    show L4161 ++ [F210] = L4158 from rfl] at h
  rw [i2323 hinj, i2321 hinj, i2322 hinj, i2324 hinj] at h
  linarith

theorem row888 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4162 + (1 : ℝ) * HLm Γ 5 L4164 + (-1 : ℝ) * HLm Γ 5 L4166 + (-1 : ℝ) * HLm Γ 5 L4168 := by
  have h := HLm_submod hΓ [F2] L4169 [F67]
  rw [show [F2] ++ L4169 ++ [F67] = L4167 from rfl, show [F2] ++ L4169 = L4163 from rfl,
    show L4169 ++ [F67] = L4165 from rfl] at h
  rw [i2327 hinj, i2325 hinj, i2326 hinj, i2328 hinj] at h
  linarith

theorem row889 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4170 + (1 : ℝ) * HLm Γ 5 L4172 + (-1 : ℝ) * HLm Γ 5 L4174 + (-1 : ℝ) * HLm Γ 5 L3215 := by
  have h := HLm_submod hΓ [F7] L4176 [F12]
  rw [show [F7] ++ L4176 ++ [F12] = L4175 from rfl, show [F7] ++ L4176 = L4171 from rfl,
    show L4176 ++ [F12] = L4173 from rfl] at h
  rw [i2331 hinj, i2329 hinj, i2330 hinj, i2332 hinj] at h
  linarith

theorem row890 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3206 + (1 : ℝ) * HLm Γ 5 L4177 + (-1 : ℝ) * HLm Γ 5 L4179 + (-1 : ℝ) * HLm Γ 5 L3162 := by
  have h := HLm_submod hΓ [F0] L3162 [F16]
  rw [show [F0] ++ L3162 ++ [F16] = L4180 from rfl, show [F0] ++ L3162 = L3206 from rfl,
    show L3162 ++ [F16] = L4178 from rfl] at h
  rw [i2334 hinj, i2333 hinj] at h
  linarith

theorem row891 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3163 + (1 : ℝ) * HLm Γ 5 L4181 + (-1 : ℝ) * HLm Γ 5 L4183 + (-1 : ℝ) * HLm Γ 5 L3162 := by
  have h := HLm_submod hΓ [F7] L3162 [F55]
  rw [show [F7] ++ L3162 ++ [F55] = L4184 from rfl, show [F7] ++ L3162 = L3163 from rfl,
    show L3162 ++ [F55] = L4182 from rfl] at h
  rw [i2336 hinj, i2335 hinj] at h
  linarith

theorem row892 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2873 + (1 : ℝ) * HLm Γ 5 L4186 + (-1 : ℝ) * HLm Γ 5 L4188 + (-1 : ℝ) * HLm Γ 5 L3182 := by
  have h := HLm_submod hΓ [F7] L3183 [F2]
  rw [show [F7] ++ L3183 ++ [F2] = L4189 from rfl, show [F7] ++ L3183 = L4185 from rfl,
    show L3183 ++ [F2] = L4187 from rfl] at h
  rw [i2339 hinj, i2337 hinj, i2338 hinj, i1800 hinj] at h
  linarith

theorem row893 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4190 + (1 : ℝ) * HLm Γ 5 L4192 + (-1 : ℝ) * HLm Γ 5 L4194 + (-1 : ℝ) * HLm Γ 5 L854 := by
  have h := HLm_submod hΓ [F210] L2501 [F43]
  rw [show [F210] ++ L2501 ++ [F43] = L4195 from rfl, show [F210] ++ L2501 = L4191 from rfl,
    show L2501 ++ [F43] = L4193 from rfl] at h
  rw [i2342 hinj, i2340 hinj, i2341 hinj, i1385 hinj] at h
  linarith

theorem row894 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3629 + (1 : ℝ) * HLm Γ 5 L4197 + (-1 : ℝ) * HLm Γ 5 L4199 + (-1 : ℝ) * HLm Γ 5 L3625 := by
  have h := HLm_submod hΓ [F16] L4201 [F67]
  rw [show [F16] ++ L4201 ++ [F67] = L4200 from rfl, show [F16] ++ L4201 = L4196 from rfl,
    show L4201 ++ [F67] = L4198 from rfl] at h
  rw [i2345 hinj, i2343 hinj, i2344 hinj, i2346 hinj] at h
  linarith

theorem row895 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1260 + (1 : ℝ) * HLm Γ 5 L3237 + (-1 : ℝ) * HLm Γ 5 L1758 + (-1 : ℝ) * HLm Γ 5 L3234 := by
  have h := HLm_submod hΓ [F62] L4205 [F67]
  rw [show [F62] ++ L4205 ++ [F67] = L4204 from rfl, show [F62] ++ L4205 = L4202 from rfl,
    show L4205 ++ [F67] = L4203 from rfl] at h
  rw [i2349 hinj, i2347 hinj, i2348 hinj, i2350 hinj] at h
  linarith

theorem row896 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4206 + (1 : ℝ) * HLm Γ 5 L4208 + (-1 : ℝ) * HLm Γ 5 L4210 + (-1 : ℝ) * HLm Γ 5 L4212 := by
  have h := HLm_submod hΓ [F7] L4213 [F86]
  rw [show [F7] ++ L4213 ++ [F86] = L4211 from rfl, show [F7] ++ L4213 = L4207 from rfl,
    show L4213 ++ [F86] = L4209 from rfl] at h
  rw [i2353 hinj, i2351 hinj, i2352 hinj, i2354 hinj] at h
  linarith

theorem row897 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4214 + (1 : ℝ) * HLm Γ 5 L4068 + (-1 : ℝ) * HLm Γ 5 L4217 + (-1 : ℝ) * HLm Γ 5 L4219 := by
  have h := HLm_submod hΓ [F7] L4220 [F45]
  rw [show [F7] ++ L4220 ++ [F45] = L4218 from rfl, show [F7] ++ L4220 = L4215 from rfl,
    show L4220 ++ [F45] = L4216 from rfl] at h
  rw [i2357 hinj, i2355 hinj, i2356 hinj, i2358 hinj] at h
  linarith

theorem row898 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4221 + (1 : ℝ) * HLm Γ 5 L2352 + (-1 : ℝ) * HLm Γ 5 L1278 + (-1 : ℝ) * HLm Γ 5 L4225 := by
  have h := HLm_submod hΓ [F1] L4225 [F16]
  rw [show [F1] ++ L4225 ++ [F16] = L4224 from rfl, show [F1] ++ L4225 = L4222 from rfl,
    show L4225 ++ [F16] = L4223 from rfl] at h
  rw [i2361 hinj, i2359 hinj, i2360 hinj] at h
  linarith

theorem row899 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4226 + (1 : ℝ) * HLm Γ 5 L4228 + (-1 : ℝ) * HLm Γ 5 L4230 + (-1 : ℝ) * HLm Γ 5 L1266 := by
  have h := HLm_submod hΓ [F210] L1267 [F45]
  rw [show [F210] ++ L1267 ++ [F45] = L4231 from rfl, show [F210] ++ L1267 = L4227 from rfl,
    show L1267 ++ [F45] = L4229 from rfl] at h
  rw [i2364 hinj, i2362 hinj, i2363 hinj, i618 hinj] at h
  linarith

end EntropyBounds.TwoSet.Certs.R7A5
