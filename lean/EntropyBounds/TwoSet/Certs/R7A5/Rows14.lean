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

theorem row2100 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2658 + (1 : ℝ) * HLm Γ 5 L8779 + (-1 : ℝ) * HLm Γ 5 L10223 + (-1 : ℝ) * HLm Γ 5 L8777 := by
  have h := HLm_submod hΓ [F9] L10225 [F210]
  rw [show [F9] ++ L10225 ++ [F210] = L10224 from rfl, show [F9] ++ L10225 = L10221 from rfl,
    show L10225 ++ [F210] = L10222 from rfl] at h
  rw [i6112 hinj, i6110 hinj, i6111 hinj, i6113 hinj] at h
  linarith

theorem row2101 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L10227 + (-1 : ℝ) * HLm Γ 5 L4558 + (-1 : ℝ) * HLm Γ 5 L8885 := by
  have h := HLm_submod hΓ [F0] L10230 [F218]
  rw [show [F0] ++ L10230 ++ [F218] = L10229 from rfl, show [F0] ++ L10230 = L10226 from rfl,
    show L10230 ++ [F218] = L10228 from rfl] at h
  rw [i6116 hinj, i6114 hinj, i6115 hinj, i6117 hinj] at h
  linarith

theorem row2102 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10227 + (1 : ℝ) * HLm Γ 5 L10232 + (-1 : ℝ) * HLm Γ 5 L10234 + (-1 : ℝ) * HLm Γ 5 L10236 := by
  have h := HLm_submod hΓ [F12] L10237 [F67]
  rw [show [F12] ++ L10237 ++ [F67] = L10235 from rfl, show [F12] ++ L10237 = L10231 from rfl,
    show L10237 ++ [F67] = L10233 from rfl] at h
  rw [i6120 hinj, i6118 hinj, i6119 hinj, i6121 hinj] at h
  linarith

theorem row2103 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5384 + (1 : ℝ) * HLm Γ 5 L8795 + (-1 : ℝ) * HLm Γ 5 L5381 + (-1 : ℝ) * HLm Γ 5 L8791 := by
  have h := HLm_submod hΓ [F0] L10241 [F45]
  rw [show [F0] ++ L10241 ++ [F45] = L10240 from rfl, show [F0] ++ L10241 = L10238 from rfl,
    show L10241 ++ [F45] = L10239 from rfl] at h
  rw [i6124 hinj, i6122 hinj, i6123 hinj, i6125 hinj] at h
  linarith

theorem row2104 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4394 + (1 : ℝ) * HLm Γ 5 L8806 + (-1 : ℝ) * HLm Γ 5 L6545 + (-1 : ℝ) * HLm Γ 5 L8804 := by
  have h := HLm_submod hΓ [F7] L10245 [F16]
  rw [show [F7] ++ L10245 ++ [F16] = L10244 from rfl, show [F7] ++ L10245 = L10242 from rfl,
    show L10245 ++ [F16] = L10243 from rfl] at h
  rw [i6128 hinj, i6126 hinj, i6127 hinj, i6129 hinj] at h
  linarith

theorem row2105 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10246 + (1 : ℝ) * HLm Γ 5 L8814 + (-1 : ℝ) * HLm Γ 5 L10249 + (-1 : ℝ) * HLm Γ 5 L8812 := by
  have h := HLm_submod hΓ [F22] L10251 [F210]
  rw [show [F22] ++ L10251 ++ [F210] = L10250 from rfl, show [F22] ++ L10251 = L10247 from rfl,
    show L10251 ++ [F210] = L10248 from rfl] at h
  rw [i6132 hinj, i6130 hinj, i6131 hinj, i6133 hinj] at h
  linarith

theorem row2106 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10252 + (1 : ℝ) * HLm Γ 5 L10254 + (-1 : ℝ) * HLm Γ 5 L10256 + (-1 : ℝ) * HLm Γ 5 L8837 := by
  have h := HLm_submod hΓ [F210] L10258 [F90]
  rw [show [F210] ++ L10258 ++ [F90] = L10257 from rfl, show [F210] ++ L10258 = L10253 from rfl,
    show L10258 ++ [F90] = L10255 from rfl] at h
  rw [i6136 hinj, i6134 hinj, i6135 hinj, i6137 hinj] at h
  linarith

theorem row2107 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L10260 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L8816 := by
  have h := HLm_submod hΓ [F0] L10263 [F67]
  rw [show [F0] ++ L10263 ++ [F67] = L10262 from rfl, show [F0] ++ L10263 = L10259 from rfl,
    show L10263 ++ [F67] = L10261 from rfl] at h
  rw [i6140 hinj, i6138 hinj, i6139 hinj, i6141 hinj] at h
  linarith

theorem row2108 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10260 + (1 : ℝ) * HLm Γ 5 L8833 + (-1 : ℝ) * HLm Γ 5 L10266 + (-1 : ℝ) * HLm Γ 5 L8831 := by
  have h := HLm_submod hΓ [F46] L8832 [F210]
  rw [show [F46] ++ L8832 ++ [F210] = L10267 from rfl, show [F46] ++ L8832 = L10264 from rfl,
    show L8832 ++ [F210] = L10265 from rfl] at h
  rw [i6144 hinj, i6142 hinj, i6143 hinj, i5211 hinj] at h
  linarith

theorem row2109 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8755 + (1 : ℝ) * HLm Γ 5 L8841 + (-1 : ℝ) * HLm Γ 5 L10270 + (-1 : ℝ) * HLm Γ 5 L8839 := by
  have h := HLm_submod hΓ [F0] L8840 [F46]
  rw [show [F0] ++ L8840 ++ [F46] = L10271 from rfl, show [F0] ++ L8840 = L10268 from rfl,
    show L8840 ++ [F46] = L10269 from rfl] at h
  rw [i6147 hinj, i6145 hinj, i6146 hinj, i5215 hinj] at h
  linarith

theorem row2110 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8755 + (1 : ℝ) * HLm Γ 5 L10273 + (-1 : ℝ) * HLm Γ 5 L10270 + (-1 : ℝ) * HLm Γ 5 L10276 := by
  have h := HLm_submod hΓ [F0] L10277 [F46]
  rw [show [F0] ++ L10277 ++ [F46] = L10275 from rfl, show [F0] ++ L10277 = L10272 from rfl,
    show L10277 ++ [F46] = L10274 from rfl] at h
  rw [i6150 hinj, i6148 hinj, i6149 hinj, i6151 hinj] at h
  linarith

theorem row2111 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8862 + (1 : ℝ) * HLm Γ 5 L10278 + (-1 : ℝ) * HLm Γ 5 L10280 + (-1 : ℝ) * HLm Γ 5 L8860 := by
  have h := HLm_submod hΓ [F210] L8861 [F30]
  rw [show [F210] ++ L8861 ++ [F30] = L10281 from rfl, show [F210] ++ L8861 = L8863 from rfl,
    show L8861 ++ [F30] = L10279 from rfl] at h
  rw [i6153 hinj, i5228 hinj, i6152 hinj, i5227 hinj] at h
  linarith

theorem row2112 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10282 + (1 : ℝ) * HLm Γ 5 L10284 + (-1 : ℝ) * HLm Γ 5 L10286 + (-1 : ℝ) * HLm Γ 5 L10288 := by
  have h := HLm_submod hΓ [F210] L10289 [F45]
  rw [show [F210] ++ L10289 ++ [F45] = L10287 from rfl, show [F210] ++ L10289 = L10283 from rfl,
    show L10289 ++ [F45] = L10285 from rfl] at h
  rw [i6156 hinj, i6154 hinj, i6155 hinj, i6157 hinj] at h
  linarith

theorem row2113 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10290 + (1 : ℝ) * HLm Γ 5 L8879 + (-1 : ℝ) * HLm Γ 5 L10293 + (-1 : ℝ) * HLm Γ 5 L8877 := by
  have h := HLm_submod hΓ [F44] L10295 [F210]
  rw [show [F44] ++ L10295 ++ [F210] = L10294 from rfl, show [F44] ++ L10295 = L10291 from rfl,
    show L10295 ++ [F210] = L10292 from rfl] at h
  rw [i6160 hinj, i6158 hinj, i6159 hinj, i6161 hinj] at h
  linarith

theorem row2114 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2670 + (1 : ℝ) * HLm Γ 5 L10297 + (-1 : ℝ) * HLm Γ 5 L9745 + (-1 : ℝ) * HLm Γ 5 L7506 := by
  have h := HLm_submod hΓ [F0] L10300 [F236]
  rw [show [F0] ++ L10300 ++ [F236] = L10299 from rfl, show [F0] ++ L10300 = L10296 from rfl,
    show L10300 ++ [F236] = L10298 from rfl] at h
  rw [i6164 hinj, i6162 hinj, i6163 hinj, i6165 hinj] at h
  linarith

theorem row2115 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L10111 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L2813 := by
  have h := HLm_submod hΓ [F0] L10304 [F210]
  rw [show [F0] ++ L10304 ++ [F210] = L10303 from rfl, show [F0] ++ L10304 = L10301 from rfl,
    show L10304 ++ [F210] = L10302 from rfl] at h
  rw [i6168 hinj, i6166 hinj, i6167 hinj, i6169 hinj] at h
  linarith

theorem row2116 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6095 + (1 : ℝ) * HLm Γ 5 L10306 + (-1 : ℝ) * HLm Γ 5 L5434 + (-1 : ℝ) * HLm Γ 5 L10309 := by
  have h := HLm_submod hΓ [F0] L10310 [F1]
  rw [show [F0] ++ L10310 ++ [F1] = L10308 from rfl, show [F0] ++ L10310 = L10305 from rfl,
    show L10310 ++ [F1] = L10307 from rfl] at h
  rw [i6172 hinj, i6170 hinj, i6171 hinj, i6173 hinj] at h
  linarith

theorem row2117 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5739 + (1 : ℝ) * HLm Γ 5 L10312 + (-1 : ℝ) * HLm Γ 5 L5515 + (-1 : ℝ) * HLm Γ 5 L10315 := by
  have h := HLm_submod hΓ [F0] L10316 [F3]
  rw [show [F0] ++ L10316 ++ [F3] = L10314 from rfl, show [F0] ++ L10316 = L10311 from rfl,
    show L10316 ++ [F3] = L10313 from rfl] at h
  rw [i6176 hinj, i6174 hinj, i6175 hinj, i6177 hinj] at h
  linarith

theorem row2118 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10317 + (1 : ℝ) * HLm Γ 5 L10319 + (-1 : ℝ) * HLm Γ 5 L10321 + (-1 : ℝ) * HLm Γ 5 L8901 := by
  have h := HLm_submod hΓ [F2] L8902 [F210]
  rw [show [F2] ++ L8902 ++ [F210] = L10322 from rfl, show [F2] ++ L8902 = L10318 from rfl,
    show L8902 ++ [F210] = L10320 from rfl] at h
  rw [i6180 hinj, i6178 hinj, i6179 hinj, i5255 hinj] at h
  linarith

theorem row2119 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4429 + (1 : ℝ) * HLm Γ 5 L10323 + (-1 : ℝ) * HLm Γ 5 L5832 + (-1 : ℝ) * HLm Γ 5 L8905 := by
  have h := HLm_submod hΓ [F0] L8906 [F3]
  rw [show [F0] ++ L8906 ++ [F3] = L10325 from rfl, show [F0] ++ L8906 = L8907 from rfl,
    show L8906 ++ [F3] = L10324 from rfl] at h
  rw [i6182 hinj, i5259 hinj, i6181 hinj, i5258 hinj] at h
  linarith

theorem row2120 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1469 + (1 : ℝ) * HLm Γ 5 L10327 + (-1 : ℝ) * HLm Γ 5 L5925 + (-1 : ℝ) * HLm Γ 5 L8932 := by
  have h := HLm_submod hΓ [F1] L10330 [F211]
  rw [show [F1] ++ L10330 ++ [F211] = L10329 from rfl, show [F1] ++ L10330 = L10326 from rfl,
    show L10330 ++ [F211] = L10328 from rfl] at h
  rw [i6185 hinj, i6183 hinj, i6184 hinj, i6186 hinj] at h
  linarith

theorem row2121 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8921 + (1 : ℝ) * HLm Γ 5 L10331 + (-1 : ℝ) * HLm Γ 5 L10333 + (-1 : ℝ) * HLm Γ 5 L8919 := by
  have h := HLm_submod hΓ [F210] L8920 [F90]
  rw [show [F210] ++ L8920 ++ [F90] = L10334 from rfl, show [F210] ++ L8920 = L8922 from rfl,
    show L8920 ++ [F90] = L10332 from rfl] at h
  rw [i6188 hinj, i5269 hinj, i6187 hinj, i5268 hinj] at h
  linarith

theorem row2122 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5739 + (1 : ℝ) * HLm Γ 5 L10336 + (-1 : ℝ) * HLm Γ 5 L5515 + (-1 : ℝ) * HLm Γ 5 L8941 := by
  have h := HLm_submod hΓ [F0] L8942 [F3]
  rw [show [F0] ++ L8942 ++ [F3] = L10338 from rfl, show [F0] ++ L8942 = L10335 from rfl,
    show L8942 ++ [F3] = L10337 from rfl] at h
  rw [i6191 hinj, i6189 hinj, i6190 hinj, i5281 hinj] at h
  linarith

theorem row2123 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8949 + (1 : ℝ) * HLm Γ 5 L10339 + (-1 : ℝ) * HLm Γ 5 L10341 + (-1 : ℝ) * HLm Γ 5 L8947 := by
  have h := HLm_submod hΓ [F2] L8948 [F67]
  rw [show [F2] ++ L8948 ++ [F67] = L10342 from rfl, show [F2] ++ L8948 = L8950 from rfl,
    show L8948 ++ [F67] = L10340 from rfl] at h
  rw [i6193 hinj, i5285 hinj, i6192 hinj, i5284 hinj] at h
  linarith

theorem row2124 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8762 + (1 : ℝ) * HLm Γ 5 L8956 + (-1 : ℝ) * HLm Γ 5 L10345 + (-1 : ℝ) * HLm Γ 5 L8954 := by
  have h := HLm_submod hΓ [F51] L10347 [F67]
  rw [show [F51] ++ L10347 ++ [F67] = L10346 from rfl, show [F51] ++ L10347 = L10343 from rfl,
    show L10347 ++ [F67] = L10344 from rfl] at h
  rw [i6196 hinj, i6194 hinj, i6195 hinj, i6197 hinj] at h
  linarith

theorem row2125 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4842 + (1 : ℝ) * HLm Γ 5 L9389 + (-1 : ℝ) * HLm Γ 5 L10008 + (-1 : ℝ) * HLm Γ 5 L9387 := by
  have h := HLm_submod hΓ [F0] L10351 [F2]
  rw [show [F0] ++ L10351 ++ [F2] = L10350 from rfl, show [F0] ++ L10351 = L10348 from rfl,
    show L10351 ++ [F2] = L10349 from rfl] at h
  rw [i6200 hinj, i6198 hinj, i6199 hinj, i6201 hinj] at h
  linarith

theorem row2126 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4274 + (1 : ℝ) * HLm Γ 5 L10353 + (-1 : ℝ) * HLm Γ 5 L10355 + (-1 : ℝ) * HLm Γ 5 L10357 := by
  have h := HLm_submod hΓ [F0] L10358 [F55]
  rw [show [F0] ++ L10358 ++ [F55] = L10356 from rfl, show [F0] ++ L10358 = L10352 from rfl,
    show L10358 ++ [F55] = L10354 from rfl] at h
  rw [i6204 hinj, i6202 hinj, i6203 hinj, i6205 hinj] at h
  linarith

theorem row2127 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8969 + (1 : ℝ) * HLm Γ 5 L10360 + (-1 : ℝ) * HLm Γ 5 L10362 + (-1 : ℝ) * HLm Γ 5 L8967 := by
  have h := HLm_submod hΓ [F210] L10364 [F17]
  rw [show [F210] ++ L10364 ++ [F17] = L10363 from rfl, show [F210] ++ L10364 = L10359 from rfl,
    show L10364 ++ [F17] = L10361 from rfl] at h
  rw [i6208 hinj, i6206 hinj, i6207 hinj, i6209 hinj] at h
  linarith

theorem row2128 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4835 + (1 : ℝ) * HLm Γ 5 L10366 + (-1 : ℝ) * HLm Γ 5 L10355 + (-1 : ℝ) * HLm Γ 5 L10369 := by
  have h := HLm_submod hΓ [F0] L10370 [F96]
  rw [show [F0] ++ L10370 ++ [F96] = L10368 from rfl, show [F0] ++ L10370 = L10365 from rfl,
    show L10370 ++ [F96] = L10367 from rfl] at h
  rw [i6212 hinj, i6210 hinj, i6211 hinj, i6213 hinj] at h
  linarith

theorem row2129 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10371 + (1 : ℝ) * HLm Γ 5 L10373 + (-1 : ℝ) * HLm Γ 5 L10375 + (-1 : ℝ) * HLm Γ 5 L8973 := by
  have h := HLm_submod hΓ [F0] L10377 [F214]
  rw [show [F0] ++ L10377 ++ [F214] = L10376 from rfl, show [F0] ++ L10377 = L10372 from rfl,
    show L10377 ++ [F214] = L10374 from rfl] at h
  rw [i6216 hinj, i6214 hinj, i6215 hinj, i6217 hinj] at h
  linarith

theorem row2130 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4298 + (1 : ℝ) * HLm Γ 5 L10379 + (-1 : ℝ) * HLm Γ 5 L5814 + (-1 : ℝ) * HLm Γ 5 L8979 := by
  have h := HLm_submod hΓ [F0] L10382 [F55]
  rw [show [F0] ++ L10382 ++ [F55] = L10381 from rfl, show [F0] ++ L10382 = L10378 from rfl,
    show L10382 ++ [F55] = L10380 from rfl] at h
  rw [i6220 hinj, i6218 hinj, i6219 hinj, i6221 hinj] at h
  linarith

theorem row2131 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4882 + (1 : ℝ) * HLm Γ 5 L6322 + (-1 : ℝ) * HLm Γ 5 L5489 + (-1 : ℝ) * HLm Γ 5 L8986 := by
  have h := HLm_submod hΓ [F0] L8987 [F12]
  rw [show [F0] ++ L8987 ++ [F12] = L10384 from rfl, show [F0] ++ L8987 = L8988 from rfl,
    show L8987 ++ [F12] = L10383 from rfl] at h
  rw [i6223 hinj, i5308 hinj, i6222 hinj, i5307 hinj] at h
  linarith

theorem row2132 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8995 + (1 : ℝ) * HLm Γ 5 L4919 + (-1 : ℝ) * HLm Γ 5 L6179 + (-1 : ℝ) * HLm Γ 5 L8993 := by
  have h := HLm_submod hΓ [F0] L8994 [F96]
  rw [show [F0] ++ L8994 ++ [F96] = L10386 from rfl, show [F0] ++ L8994 = L8996 from rfl,
    show L8994 ++ [F96] = L10385 from rfl] at h
  rw [i6225 hinj, i5312 hinj, i6224 hinj, i5311 hinj] at h
  linarith

theorem row2133 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9011 + (1 : ℝ) * HLm Γ 5 L10387 + (-1 : ℝ) * HLm Γ 5 L10389 + (-1 : ℝ) * HLm Γ 5 L9009 := by
  have h := HLm_submod hΓ [F0] L9010 [F82]
  rw [show [F0] ++ L9010 ++ [F82] = L10390 from rfl, show [F0] ++ L9010 = L9012 from rfl,
    show L9010 ++ [F82] = L10388 from rfl] at h
  rw [i6227 hinj, i5322 hinj, i6226 hinj, i5321 hinj] at h
  linarith

theorem row2134 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9015 + (1 : ℝ) * HLm Γ 5 L10391 + (-1 : ℝ) * HLm Γ 5 L10393 + (-1 : ℝ) * HLm Γ 5 L9013 := by
  have h := HLm_submod hΓ [F0] L9014 [F236]
  rw [show [F0] ++ L9014 ++ [F236] = L10394 from rfl, show [F0] ++ L9014 = L9016 from rfl,
    show L9014 ++ [F236] = L10392 from rfl] at h
  rw [i6229 hinj, i5324 hinj, i6228 hinj, i5323 hinj] at h
  linarith

theorem row2135 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L9923 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L9928 := by
  have h := HLm_submod hΓ [F1] L10398 [F210]
  rw [show [F1] ++ L10398 ++ [F210] = L10397 from rfl, show [F1] ++ L10398 = L10395 from rfl,
    show L10398 ++ [F210] = L10396 from rfl] at h
  rw [i6232 hinj, i6230 hinj, i6231 hinj, i6233 hinj] at h
  linarith

theorem row2136 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9035 + (1 : ℝ) * HLm Γ 5 L10400 + (-1 : ℝ) * HLm Γ 5 L10402 + (-1 : ℝ) * HLm Γ 5 L9031 := by
  have h := HLm_submod hΓ [F210] L10404 [F27]
  rw [show [F210] ++ L10404 ++ [F27] = L10403 from rfl, show [F210] ++ L10404 = L10399 from rfl,
    show L10404 ++ [F27] = L10401 from rfl] at h
  rw [i6236 hinj, i6234 hinj, i6235 hinj, i6237 hinj] at h
  linarith

theorem row2137 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10405 + (1 : ℝ) * HLm Γ 5 L10407 + (-1 : ℝ) * HLm Γ 5 L10409 + (-1 : ℝ) * HLm Γ 5 L10411 := by
  have h := HLm_submod hΓ [F107] L10412 [F210]
  rw [show [F107] ++ L10412 ++ [F210] = L10410 from rfl, show [F107] ++ L10412 = L10406 from rfl,
    show L10412 ++ [F210] = L10408 from rfl] at h
  rw [i6240 hinj, i6238 hinj, i6239 hinj, i6241 hinj] at h
  linarith

theorem row2138 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10413 + (1 : ℝ) * HLm Γ 5 L10415 + (-1 : ℝ) * HLm Γ 5 L10417 + (-1 : ℝ) * HLm Γ 5 L10419 := by
  have h := HLm_submod hΓ [F7] L10420 [F6]
  rw [show [F7] ++ L10420 ++ [F6] = L10418 from rfl, show [F7] ++ L10420 = L10414 from rfl,
    show L10420 ++ [F6] = L10416 from rfl] at h
  rw [i6244 hinj, i6242 hinj, i6243 hinj, i6245 hinj] at h
  linarith

theorem row2139 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10421 + (1 : ℝ) * HLm Γ 5 L10423 + (-1 : ℝ) * HLm Γ 5 L10425 + (-1 : ℝ) * HLm Γ 5 L10427 := by
  have h := HLm_submod hΓ [F210] L10428 [F17]
  rw [show [F210] ++ L10428 ++ [F17] = L10426 from rfl, show [F210] ++ L10428 = L10422 from rfl,
    show L10428 ++ [F17] = L10424 from rfl] at h
  rw [i6248 hinj, i6246 hinj, i6247 hinj, i6249 hinj] at h
  linarith

theorem row2140 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10429 + (1 : ℝ) * HLm Γ 5 L9027 + (-1 : ℝ) * HLm Γ 5 L10432 + (-1 : ℝ) * HLm Γ 5 L9025 := by
  have h := HLm_submod hΓ [F107] L9026 [F210]
  rw [show [F107] ++ L9026 ++ [F210] = L10433 from rfl, show [F107] ++ L9026 = L10430 from rfl,
    show L9026 ++ [F210] = L10431 from rfl] at h
  rw [i6252 hinj, i6250 hinj, i6251 hinj, i5330 hinj] at h
  linarith

theorem row2141 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9040 + (1 : ℝ) * HLm Γ 5 L10435 + (-1 : ℝ) * HLm Γ 5 L10437 + (-1 : ℝ) * HLm Γ 5 L9038 := by
  have h := HLm_submod hΓ [F67] L10439 [F27]
  rw [show [F67] ++ L10439 ++ [F27] = L10438 from rfl, show [F67] ++ L10439 = L10434 from rfl,
    show L10439 ++ [F27] = L10436 from rfl] at h
  rw [i6255 hinj, i6253 hinj, i6254 hinj, i6256 hinj] at h
  linarith

theorem row2142 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10440 + (1 : ℝ) * HLm Γ 5 L9428 + (-1 : ℝ) * HLm Γ 5 L10443 + (-1 : ℝ) * HLm Γ 5 L9424 := by
  have h := HLm_submod hΓ [F9] L10445 [F210]
  rw [show [F9] ++ L10445 ++ [F210] = L10444 from rfl, show [F9] ++ L10445 = L10441 from rfl,
    show L10445 ++ [F210] = L10442 from rfl] at h
  rw [i6259 hinj, i6257 hinj, i6258 hinj, i6260 hinj] at h
  linarith

theorem row2143 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L9057 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L9055 := by
  have h := HLm_submod hΓ [F0] L9056 [F67]
  rw [show [F0] ++ L9056 ++ [F67] = L10448 from rfl, show [F0] ++ L9056 = L10446 from rfl,
    show L9056 ++ [F67] = L10447 from rfl] at h
  rw [i6263 hinj, i6261 hinj, i6262 hinj, i5349 hinj] at h
  linarith

theorem row2144 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10449 + (1 : ℝ) * HLm Γ 5 L5016 + (-1 : ℝ) * HLm Γ 5 L9686 + (-1 : ℝ) * HLm Γ 5 L5014 := by
  have h := HLm_submod hΓ [F0] L6250 [F67]
  rw [show [F0] ++ L6250 ++ [F67] = L10451 from rfl, show [F0] ++ L6250 = L10450 from rfl,
    show L6250 ++ [F67] = L6248 from rfl] at h
  rw [i6265 hinj, i6264 hinj, i3598 hinj, i3600 hinj] at h
  linarith

theorem row2145 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9057 + (1 : ℝ) * HLm Γ 5 L9068 + (-1 : ℝ) * HLm Γ 5 L10454 + (-1 : ℝ) * HLm Γ 5 L9066 := by
  have h := HLm_submod hΓ [F3] L9067 [F210]
  rw [show [F3] ++ L9067 ++ [F210] = L10455 from rfl, show [F3] ++ L9067 = L10452 from rfl,
    show L9067 ++ [F210] = L10453 from rfl] at h
  rw [i6268 hinj, i6266 hinj, i6267 hinj, i5356 hinj] at h
  linarith

theorem row2146 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10456 + (1 : ℝ) * HLm Γ 5 L10458 + (-1 : ℝ) * HLm Γ 5 L10460 + (-1 : ℝ) * HLm Γ 5 L10462 := by
  have h := HLm_submod hΓ [F210] L10463 [F36]
  rw [show [F210] ++ L10463 ++ [F36] = L10461 from rfl, show [F210] ++ L10463 = L10457 from rfl,
    show L10463 ++ [F36] = L10459 from rfl] at h
  rw [i6271 hinj, i6269 hinj, i6270 hinj, i6272 hinj] at h
  linarith

theorem row2147 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3517 + (1 : ℝ) * HLm Γ 5 L9161 + (-1 : ℝ) * HLm Γ 5 L4558 + (-1 : ℝ) * HLm Γ 5 L9158 := by
  have h := HLm_submod hΓ [F0] L10467 [F16]
  rw [show [F0] ++ L10467 ++ [F16] = L10466 from rfl, show [F0] ++ L10467 = L10464 from rfl,
    show L10467 ++ [F16] = L10465 from rfl] at h
  rw [i6275 hinj, i6273 hinj, i6274 hinj, i6276 hinj] at h
  linarith

theorem row2148 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9552 + (1 : ℝ) * HLm Γ 5 L10469 + (-1 : ℝ) * HLm Γ 5 L10471 + (-1 : ℝ) * HLm Γ 5 L9549 := by
  have h := HLm_submod hΓ [F210] L10473 [F17]
  rw [show [F210] ++ L10473 ++ [F17] = L10472 from rfl, show [F210] ++ L10473 = L10468 from rfl,
    show L10473 ++ [F17] = L10470 from rfl] at h
  rw [i6279 hinj, i6277 hinj, i6278 hinj, i6280 hinj] at h
  linarith

theorem row2149 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5927 + (1 : ℝ) * HLm Γ 5 L10475 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10478 := by
  have h := HLm_submod hΓ [F1] L10479 [F10]
  rw [show [F1] ++ L10479 ++ [F10] = L10477 from rfl, show [F1] ++ L10479 = L10474 from rfl,
    show L10479 ++ [F10] = L10476 from rfl] at h
  rw [i6283 hinj, i6281 hinj, i6282 hinj, i6284 hinj] at h
  linarith

theorem row2150 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5927 + (1 : ℝ) * HLm Γ 5 L10481 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10484 := by
  have h := HLm_submod hΓ [F1] L10485 [F17]
  rw [show [F1] ++ L10485 ++ [F17] = L10483 from rfl, show [F1] ++ L10485 = L10480 from rfl,
    show L10485 ++ [F17] = L10482 from rfl] at h
  rw [i6287 hinj, i6285 hinj, i6286 hinj, i6288 hinj] at h
  linarith

theorem row2151 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10486 + (1 : ℝ) * HLm Γ 5 L10488 + (-1 : ℝ) * HLm Γ 5 L10490 + (-1 : ℝ) * HLm Γ 5 L10492 := by
  have h := HLm_submod hΓ [F7] L10493 [F210]
  rw [show [F7] ++ L10493 ++ [F210] = L10491 from rfl, show [F7] ++ L10493 = L10487 from rfl,
    show L10493 ++ [F210] = L10489 from rfl] at h
  rw [i6291 hinj, i6289 hinj, i6290 hinj, i6292 hinj] at h
  linarith

theorem row2152 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L9083 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L9081 := by
  have h := HLm_submod hΓ [F10] L10497 [F210]
  rw [show [F10] ++ L10497 ++ [F210] = L10496 from rfl, show [F10] ++ L10497 = L10494 from rfl,
    show L10497 ++ [F210] = L10495 from rfl] at h
  rw [i6295 hinj, i6293 hinj, i6294 hinj, i6296 hinj] at h
  linarith

theorem row2153 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5927 + (1 : ℝ) * HLm Γ 5 L9090 + (-1 : ℝ) * HLm Γ 5 L5931 + (-1 : ℝ) * HLm Γ 5 L9088 := by
  have h := HLm_submod hΓ [F1] L10501 [F7]
  rw [show [F1] ++ L10501 ++ [F7] = L10500 from rfl, show [F1] ++ L10501 = L10498 from rfl,
    show L10501 ++ [F7] = L10499 from rfl] at h
  rw [i6299 hinj, i6297 hinj, i6298 hinj, i6300 hinj] at h
  linarith

theorem row2154 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10502 + (1 : ℝ) * HLm Γ 5 L9102 + (-1 : ℝ) * HLm Γ 5 L10505 + (-1 : ℝ) * HLm Γ 5 L9098 := by
  have h := HLm_submod hΓ [F0] L10507 [F45]
  rw [show [F0] ++ L10507 ++ [F45] = L10506 from rfl, show [F0] ++ L10507 = L10503 from rfl,
    show L10507 ++ [F45] = L10504 from rfl] at h
  rw [i6303 hinj, i6301 hinj, i6302 hinj, i6304 hinj] at h
  linarith

theorem row2155 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5922 + (1 : ℝ) * HLm Γ 5 L9332 + (-1 : ℝ) * HLm Γ 5 L5925 + (-1 : ℝ) * HLm Γ 5 L3696 := by
  have h := HLm_submod hΓ [F1] L10511 [F9]
  rw [show [F1] ++ L10511 ++ [F9] = L10510 from rfl, show [F1] ++ L10511 = L10508 from rfl,
    show L10511 ++ [F9] = L10509 from rfl] at h
  rw [i6307 hinj, i6305 hinj, i6306 hinj, i6308 hinj] at h
  linarith

theorem row2156 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10512 + (1 : ℝ) * HLm Γ 5 L10514 + (-1 : ℝ) * HLm Γ 5 L10516 + (-1 : ℝ) * HLm Γ 5 L10518 := by
  have h := HLm_submod hΓ [F210] L10519 [F90]
  rw [show [F210] ++ L10519 ++ [F90] = L10517 from rfl, show [F210] ++ L10519 = L10513 from rfl,
    show L10519 ++ [F90] = L10515 from rfl] at h
  rw [i6311 hinj, i6309 hinj, i6310 hinj, i6312 hinj] at h
  linarith

theorem row2157 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10520 + (1 : ℝ) * HLm Γ 5 L10522 + (-1 : ℝ) * HLm Γ 5 L6782 + (-1 : ℝ) * HLm Γ 5 L10525 := by
  have h := HLm_submod hΓ [F7] L10526 [F85]
  rw [show [F7] ++ L10526 ++ [F85] = L10524 from rfl, show [F7] ++ L10526 = L10521 from rfl,
    show L10526 ++ [F85] = L10523 from rfl] at h
  rw [i6315 hinj, i6313 hinj, i6314 hinj, i6316 hinj] at h
  linarith

theorem row2158 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1719 + (1 : ℝ) * HLm Γ 5 L10528 + (-1 : ℝ) * HLm Γ 5 L5931 + (-1 : ℝ) * HLm Γ 5 L10531 := by
  have h := HLm_submod hΓ [F1] L10532 [F210]
  rw [show [F1] ++ L10532 ++ [F210] = L10530 from rfl, show [F1] ++ L10532 = L10527 from rfl,
    show L10532 ++ [F210] = L10529 from rfl] at h
  rw [i6319 hinj, i6317 hinj, i6318 hinj, i6320 hinj] at h
  linarith

theorem row2159 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10533 + (1 : ℝ) * HLm Γ 5 L10535 + (-1 : ℝ) * HLm Γ 5 L10537 + (-1 : ℝ) * HLm Γ 5 L10539 := by
  have h := HLm_submod hΓ [F214] L10540 [F33]
  rw [show [F214] ++ L10540 ++ [F33] = L10538 from rfl, show [F214] ++ L10540 = L10534 from rfl,
    show L10540 ++ [F33] = L10536 from rfl] at h
  rw [i6323 hinj, i6321 hinj, i6322 hinj, i6324 hinj] at h
  linarith

theorem row2160 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9908 + (1 : ℝ) * HLm Γ 5 L9154 + (-1 : ℝ) * HLm Γ 5 L9912 + (-1 : ℝ) * HLm Γ 5 L9150 := by
  have h := HLm_submod hΓ [F1] L10544 [F85]
  rw [show [F1] ++ L10544 ++ [F85] = L10543 from rfl, show [F1] ++ L10544 = L10541 from rfl,
    show L10544 ++ [F85] = L10542 from rfl] at h
  rw [i6327 hinj, i6325 hinj, i6326 hinj, i6328 hinj] at h
  linarith

theorem row2161 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10545 + (1 : ℝ) * HLm Γ 5 L10547 + (-1 : ℝ) * HLm Γ 5 L10549 + (-1 : ℝ) * HLm Γ 5 L9152 := by
  have h := HLm_submod hΓ [F210] L9153 [F33]
  rw [show [F210] ++ L9153 ++ [F33] = L10550 from rfl, show [F210] ++ L9153 = L10546 from rfl,
    show L9153 ++ [F33] = L10548 from rfl] at h
  rw [i6331 hinj, i6329 hinj, i6330 hinj, i5410 hinj] at h
  linarith

theorem row2162 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10551 + (1 : ℝ) * HLm Γ 5 L9546 + (-1 : ℝ) * HLm Γ 5 L10553 + (-1 : ℝ) * HLm Γ 5 L9542 := by
  have h := HLm_submod hΓ [F108] L9543 [F210]
  rw [show [F108] ++ L9543 ++ [F210] = L10554 from rfl, show [F108] ++ L9543 = L10552 from rfl,
    show L9543 ++ [F210] = L9547 from rfl] at h
  rw [i6333 hinj, i6332 hinj, i5645 hinj, i5643 hinj] at h
  linarith

theorem row2163 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10555 + (1 : ℝ) * HLm Γ 5 L9276 + (-1 : ℝ) * HLm Γ 5 L6582 + (-1 : ℝ) * HLm Γ 5 L9273 := by
  have h := HLm_submod hΓ [F7] L10559 [F210]
  rw [show [F7] ++ L10559 ++ [F210] = L10558 from rfl, show [F7] ++ L10559 = L10556 from rfl,
    show L10559 ++ [F210] = L10557 from rfl] at h
  rw [i6336 hinj, i6334 hinj, i6335 hinj, i6337 hinj] at h
  linarith

theorem row2164 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L8819 + (1 : ℝ) * HLm Γ 5 L10561 + (-1 : ℝ) * HLm Γ 5 L10266 + (-1 : ℝ) * HLm Γ 5 L9169 := by
  have h := HLm_submod hΓ [F47] L9170 [F67]
  rw [show [F47] ++ L9170 ++ [F67] = L10563 from rfl, show [F47] ++ L9170 = L10560 from rfl,
    show L9170 ++ [F67] = L10562 from rfl] at h
  rw [i6340 hinj, i6338 hinj, i6339 hinj, i5420 hinj] at h
  linarith

theorem row2165 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10564 + (1 : ℝ) * HLm Γ 5 L9187 + (-1 : ℝ) * HLm Γ 5 L10567 + (-1 : ℝ) * HLm Γ 5 L9183 := by
  have h := HLm_submod hΓ [F7] L10569 [F85]
  rw [show [F7] ++ L10569 ++ [F85] = L10568 from rfl, show [F7] ++ L10569 = L10565 from rfl,
    show L10569 ++ [F85] = L10566 from rfl] at h
  rw [i6343 hinj, i6341 hinj, i6342 hinj, i6344 hinj] at h
  linarith

theorem row2166 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9179 + (1 : ℝ) * HLm Γ 5 L5102 + (-1 : ℝ) * HLm Γ 5 L6320 + (-1 : ℝ) * HLm Γ 5 L9177 := by
  have h := HLm_submod hΓ [F7] L9178 [F47]
  rw [show [F7] ++ L9178 ++ [F47] = L10571 from rfl, show [F7] ++ L9178 = L9180 from rfl,
    show L9178 ++ [F47] = L10570 from rfl] at h
  rw [i6346 hinj, i5425 hinj, i6345 hinj, i5424 hinj] at h
  linarith

theorem row2167 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10572 + (1 : ℝ) * HLm Γ 5 L10574 + (-1 : ℝ) * HLm Γ 5 L10576 + (-1 : ℝ) * HLm Γ 5 L9185 := by
  have h := HLm_submod hΓ [F210] L9186 [F27]
  rw [show [F210] ++ L9186 ++ [F27] = L10577 from rfl, show [F210] ++ L9186 = L10573 from rfl,
    show L9186 ++ [F27] = L10575 from rfl] at h
  rw [i6349 hinj, i6347 hinj, i6348 hinj, i5428 hinj] at h
  linarith

theorem row2168 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9194 + (1 : ℝ) * HLm Γ 5 L10578 + (-1 : ℝ) * HLm Γ 5 L10580 + (-1 : ℝ) * HLm Γ 5 L9192 := by
  have h := HLm_submod hΓ [F210] L9193 [F55]
  rw [show [F210] ++ L9193 ++ [F55] = L10581 from rfl, show [F210] ++ L9193 = L9195 from rfl,
    show L9193 ++ [F55] = L10579 from rfl] at h
  rw [i6351 hinj, i5433 hinj, i6350 hinj, i5432 hinj] at h
  linarith

theorem row2169 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1694 + (1 : ℝ) * HLm Γ 5 L9394 + (-1 : ℝ) * HLm Γ 5 L6396 + (-1 : ℝ) * HLm Γ 5 L9391 := by
  have h := HLm_submod hΓ [F0] L9392 [F210]
  rw [show [F0] ++ L9392 ++ [F210] = L10583 from rfl, show [F0] ++ L9392 = L10582 from rfl,
    show L9392 ++ [F210] = L9395 from rfl] at h
  rw [i6353 hinj, i6352 hinj, i5551 hinj, i5549 hinj] at h
  linarith

theorem row2170 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10584 + (1 : ℝ) * HLm Γ 5 L9218 + (-1 : ℝ) * HLm Γ 5 L10587 + (-1 : ℝ) * HLm Γ 5 L9216 := by
  have h := HLm_submod hΓ [F107] L9217 [F210]
  rw [show [F107] ++ L9217 ++ [F210] = L10588 from rfl, show [F107] ++ L9217 = L10585 from rfl,
    show L9217 ++ [F210] = L10586 from rfl] at h
  rw [i6356 hinj, i6354 hinj, i6355 hinj, i5444 hinj] at h
  linarith

theorem row2171 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10589 + (1 : ℝ) * HLm Γ 5 L9226 + (-1 : ℝ) * HLm Γ 5 L10592 + (-1 : ℝ) * HLm Γ 5 L9224 := by
  have h := HLm_submod hΓ [F3] L9225 [F210]
  rw [show [F3] ++ L9225 ++ [F210] = L10593 from rfl, show [F3] ++ L9225 = L10590 from rfl,
    show L9225 ++ [F210] = L10591 from rfl] at h
  rw [i6359 hinj, i6357 hinj, i6358 hinj, i5448 hinj] at h
  linarith

theorem row2172 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10594 + (1 : ℝ) * HLm Γ 5 L9271 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L9269 := by
  have h := HLm_submod hΓ [F0] L10598 [F44]
  rw [show [F0] ++ L10598 ++ [F44] = L10597 from rfl, show [F0] ++ L10598 = L10595 from rfl,
    show L10598 ++ [F44] = L10596 from rfl] at h
  rw [i6362 hinj, i6360 hinj, i6361 hinj, i6363 hinj] at h
  linarith

theorem row2173 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10599 + (1 : ℝ) * HLm Γ 5 L10601 + (-1 : ℝ) * HLm Γ 5 L6403 + (-1 : ℝ) * HLm Γ 5 L10604 := by
  have h := HLm_submod hΓ [F0] L10605 [F12]
  rw [show [F0] ++ L10605 ++ [F12] = L10603 from rfl, show [F0] ++ L10605 = L10600 from rfl,
    show L10605 ++ [F12] = L10602 from rfl] at h
  rw [i6366 hinj, i6364 hinj, i6365 hinj, i6367 hinj] at h
  linarith

theorem row2174 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5927 + (1 : ℝ) * HLm Γ 5 L9297 + (-1 : ℝ) * HLm Γ 5 L5931 + (-1 : ℝ) * HLm Γ 5 L9295 := by
  have h := HLm_submod hΓ [F1] L9296 [F7]
  rw [show [F1] ++ L9296 ++ [F7] = L10608 from rfl, show [F1] ++ L9296 = L10606 from rfl,
    show L9296 ++ [F7] = L10607 from rfl] at h
  rw [i6370 hinj, i6368 hinj, i6369 hinj, i5492 hinj] at h
  linarith

theorem row2175 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10609 + (1 : ℝ) * HLm Γ 5 L9453 + (-1 : ℝ) * HLm Γ 5 L10611 + (-1 : ℝ) * HLm Γ 5 L9449 := by
  have h := HLm_submod hΓ [F9] L9450 [F210]
  rw [show [F9] ++ L9450 ++ [F210] = L10612 from rfl, show [F9] ++ L9450 = L10610 from rfl,
    show L9450 ++ [F210] = L9454 from rfl] at h
  rw [i6372 hinj, i6371 hinj, i5585 hinj, i5583 hinj] at h
  linarith

theorem row2176 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9309 + (1 : ℝ) * HLm Γ 5 L5700 + (-1 : ℝ) * HLm Γ 5 L6352 + (-1 : ℝ) * HLm Γ 5 L9307 := by
  have h := HLm_submod hΓ [F0] L9308 [F7]
  rw [show [F0] ++ L9308 ++ [F7] = L10614 from rfl, show [F0] ++ L9308 = L9310 from rfl,
    show L9308 ++ [F7] = L10613 from rfl] at h
  rw [i6374 hinj, i5500 hinj, i6373 hinj, i5499 hinj] at h
  linarith

theorem row2177 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10615 + (1 : ℝ) * HLm Γ 5 L9400 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L9396 := by
  have h := HLm_submod hΓ [F0] L10619 [F90]
  rw [show [F0] ++ L10619 ++ [F90] = L10618 from rfl, show [F0] ++ L10619 = L10616 from rfl,
    show L10619 ++ [F90] = L10617 from rfl] at h
  rw [i6377 hinj, i6375 hinj, i6376 hinj, i6378 hinj] at h
  linarith

theorem row2178 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5739 + (1 : ℝ) * HLm Γ 5 L10621 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L9379 := by
  have h := HLm_submod hΓ [F0] L9380 [F4]
  rw [show [F0] ++ L9380 ++ [F4] = L10623 from rfl, show [F0] ++ L9380 = L10620 from rfl,
    show L9380 ++ [F4] = L10622 from rfl] at h
  rw [i6381 hinj, i6379 hinj, i6380 hinj, i5543 hinj] at h
  linarith

theorem row2179 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1694 + (1 : ℝ) * HLm Γ 5 L9537 + (-1 : ℝ) * HLm Γ 5 L6403 + (-1 : ℝ) * HLm Γ 5 L9534 := by
  have h := HLm_submod hΓ [F0] L10627 [F228]
  rw [show [F0] ++ L10627 ++ [F228] = L10626 from rfl, show [F0] ++ L10627 = L10624 from rfl,
    show L10627 ++ [F228] = L10625 from rfl] at h
  rw [i6384 hinj, i6382 hinj, i6383 hinj, i6385 hinj] at h
  linarith

theorem row2180 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10628 + (1 : ℝ) * HLm Γ 5 L9408 + (-1 : ℝ) * HLm Γ 5 L10631 + (-1 : ℝ) * HLm Γ 5 L9406 := by
  have h := HLm_submod hΓ [F51] L10633 [F210]
  rw [show [F51] ++ L10633 ++ [F210] = L10632 from rfl, show [F51] ++ L10633 = L10629 from rfl,
    show L10633 ++ [F210] = L10630 from rfl] at h
  rw [i6388 hinj, i6386 hinj, i6387 hinj, i6389 hinj] at h
  linarith

theorem row2181 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10634 + (1 : ℝ) * HLm Γ 5 L9442 + (-1 : ℝ) * HLm Γ 5 L4252 + (-1 : ℝ) * HLm Γ 5 L9440 := by
  have h := HLm_submod hΓ [F1] L10638 [F2]
  rw [show [F1] ++ L10638 ++ [F2] = L10637 from rfl, show [F1] ++ L10638 = L10635 from rfl,
    show L10638 ++ [F2] = L10636 from rfl] at h
  rw [i6392 hinj, i6390 hinj, i6391 hinj, i6393 hinj] at h
  linarith

theorem row2182 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5739 + (1 : ℝ) * HLm Γ 5 L9513 + (-1 : ℝ) * HLm Γ 5 L5489 + (-1 : ℝ) * HLm Γ 5 L9511 := by
  have h := HLm_submod hΓ [F0] L10642 [F2]
  rw [show [F0] ++ L10642 ++ [F2] = L10641 from rfl, show [F0] ++ L10642 = L10639 from rfl,
    show L10642 ++ [F2] = L10640 from rfl] at h
  rw [i6396 hinj, i6394 hinj, i6395 hinj, i6397 hinj] at h
  linarith

theorem row2183 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1894 + (1 : ℝ) * HLm Γ 5 L9467 + (-1 : ℝ) * HLm Γ 5 L5434 + (-1 : ℝ) * HLm Γ 5 L9465 := by
  have h := HLm_submod hΓ [F0] L10646 [F214]
  rw [show [F0] ++ L10646 ++ [F214] = L10645 from rfl, show [F0] ++ L10646 = L10643 from rfl,
    show L10646 ++ [F214] = L10644 from rfl] at h
  rw [i6400 hinj, i6398 hinj, i6399 hinj, i6401 hinj] at h
  linarith

theorem row2184 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10647 + (1 : ℝ) * HLm Γ 5 L9475 + (-1 : ℝ) * HLm Γ 5 L10650 + (-1 : ℝ) * HLm Γ 5 L9473 := by
  have h := HLm_submod hΓ [F62] L10652 [F210]
  rw [show [F62] ++ L10652 ++ [F210] = L10651 from rfl, show [F62] ++ L10652 = L10648 from rfl,
    show L10652 ++ [F210] = L10649 from rfl] at h
  rw [i6404 hinj, i6402 hinj, i6403 hinj, i6405 hinj] at h
  linarith

theorem row2185 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9482 + (1 : ℝ) * HLm Γ 5 L6356 + (-1 : ℝ) * HLm Γ 5 L5931 + (-1 : ℝ) * HLm Γ 5 L9480 := by
  have h := HLm_submod hΓ [F1] L9481 [F2]
  rw [show [F1] ++ L9481 ++ [F2] = L10654 from rfl, show [F1] ++ L9481 = L9483 from rfl,
    show L9481 ++ [F2] = L10653 from rfl] at h
  rw [i6407 hinj, i5601 hinj, i6406 hinj, i5600 hinj] at h
  linarith

theorem row2186 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10655 + (1 : ℝ) * HLm Γ 5 L10657 + (-1 : ℝ) * HLm Γ 5 L10659 + (-1 : ℝ) * HLm Γ 5 L10661 := by
  have h := HLm_submod hΓ [F7] L10662 [F43]
  rw [show [F7] ++ L10662 ++ [F43] = L10660 from rfl, show [F7] ++ L10662 = L10656 from rfl,
    show L10662 ++ [F43] = L10658 from rfl] at h
  rw [i6410 hinj, i6408 hinj, i6409 hinj, i6411 hinj] at h
  linarith

theorem row2187 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L9568 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L9565 := by
  have h := HLm_submod hΓ [F7] L10666 [F210]
  rw [show [F7] ++ L10666 ++ [F210] = L10665 from rfl, show [F7] ++ L10666 = L10663 from rfl,
    show L10666 ++ [F210] = L10664 from rfl] at h
  rw [i6414 hinj, i6412 hinj, i6413 hinj, i6415 hinj] at h
  linarith

theorem row2188 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L10270 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L1350 := by
  have h := HLm_submod hΓ [F7] L9570 [F210]
  rw [show [F7] ++ L9570 ++ [F210] = L10668 from rfl, show [F7] ++ L9570 = L9571 from rfl,
    show L9570 ++ [F210] = L10667 from rfl] at h
  rw [i6417 hinj, i5662 hinj, i6416 hinj, i5661 hinj] at h
  linarith

theorem row2189 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L9671 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L1301 := by
  have h := HLm_submod hΓ [F7] L10672 [F210]
  rw [show [F7] ++ L10672 ++ [F210] = L10671 from rfl, show [F7] ++ L10672 = L10669 from rfl,
    show L10672 ++ [F210] = L10670 from rfl] at h
  rw [i6420 hinj, i6418 hinj, i6419 hinj, i6421 hinj] at h
  linarith

theorem row2190 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L10094 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L8132 := by
  have h := HLm_submod hΓ [F1] L10676 [F210]
  rw [show [F1] ++ L10676 ++ [F210] = L10675 from rfl, show [F1] ++ L10676 = L10673 from rfl,
    show L10676 ++ [F210] = L10674 from rfl] at h
  rw [i6424 hinj, i6422 hinj, i6423 hinj, i6425 hinj] at h
  linarith

theorem row2191 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4558 + (1 : ℝ) * HLm Γ 5 L9588 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L9586 := by
  have h := HLm_submod hΓ [F1] L10680 [F67]
  rw [show [F1] ++ L10680 ++ [F67] = L10679 from rfl, show [F1] ++ L10680 = L10677 from rfl,
    show L10680 ++ [F67] = L10678 from rfl] at h
  rw [i6428 hinj, i6426 hinj, i6427 hinj, i6429 hinj] at h
  linarith

theorem row2192 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4252 + (1 : ℝ) * HLm Γ 5 L10008 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5249 := by
  have h := HLm_submod hΓ [F1] L10684 [F7]
  rw [show [F1] ++ L10684 ++ [F7] = L10683 from rfl, show [F1] ++ L10684 = L10681 from rfl,
    show L10684 ++ [F7] = L10682 from rfl] at h
  rw [i6432 hinj, i6430 hinj, i6431 hinj, i6433 hinj] at h
  linarith

theorem row2193 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L9686 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L9683 := by
  have h := HLm_submod hΓ [F1] L10688 [F210]
  rw [show [F1] ++ L10688 ++ [F210] = L10687 from rfl, show [F1] ++ L10688 = L10685 from rfl,
    show L10688 ++ [F210] = L10686 from rfl] at h
  rw [i6436 hinj, i6434 hinj, i6435 hinj, i6437 hinj] at h
  linarith

theorem row2194 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4558 + (1 : ℝ) * HLm Γ 5 L9686 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10449 := by
  have h := HLm_submod hΓ [F1] L10450 [F67]
  rw [show [F1] ++ L10450 ++ [F67] = L10690 from rfl, show [F1] ++ L10450 = L10689 from rfl,
    show L10450 ++ [F67] = L10451 from rfl] at h
  rw [i6439 hinj, i6438 hinj, i6265 hinj, i6264 hinj] at h
  linarith

theorem row2195 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L9613 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L9610 := by
  have h := HLm_submod hΓ [F1] L10694 [F210]
  rw [show [F1] ++ L10694 ++ [F210] = L10693 from rfl, show [F1] ++ L10694 = L10691 from rfl,
    show L10694 ++ [F210] = L10692 from rfl] at h
  rw [i6442 hinj, i6440 hinj, i6441 hinj, i6443 hinj] at h
  linarith

theorem row2196 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4558 + (1 : ℝ) * HLm Γ 5 L9692 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L9689 := by
  have h := HLm_submod hΓ [F1] L10698 [F67]
  rw [show [F1] ++ L10698 ++ [F67] = L10697 from rfl, show [F1] ++ L10698 = L10695 from rfl,
    show L10698 ++ [F67] = L10696 from rfl] at h
  rw [i6446 hinj, i6444 hinj, i6445 hinj, i6447 hinj] at h
  linarith

theorem row2197 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L9604 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L9602 := by
  have h := HLm_submod hΓ [F1] L9603 [F210]
  rw [show [F1] ++ L9603 ++ [F210] = L10701 from rfl, show [F1] ++ L9603 = L10699 from rfl,
    show L9603 ++ [F210] = L10700 from rfl] at h
  rw [i6450 hinj, i6448 hinj, i6449 hinj, i5685 hinj] at h
  linarith

theorem row2198 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4252 + (1 : ℝ) * HLm Γ 5 L10703 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10706 := by
  have h := HLm_submod hΓ [F1] L10707 [F7]
  rw [show [F1] ++ L10707 ++ [F7] = L10705 from rfl, show [F1] ++ L10707 = L10702 from rfl,
    show L10707 ++ [F7] = L10704 from rfl] at h
  rw [i6453 hinj, i6451 hinj, i6452 hinj, i6454 hinj] at h
  linarith

theorem row2199 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L10708 + (1 : ℝ) * HLm Γ 5 L10710 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10713 := by
  have h := HLm_submod hΓ [F1] L10714 [F7]
  rw [show [F1] ++ L10714 ++ [F7] = L10712 from rfl, show [F1] ++ L10714 = L10709 from rfl,
    show L10714 ++ [F7] = L10711 from rfl] at h
  rw [i6457 hinj, i6455 hinj, i6456 hinj, i6458 hinj] at h
  linarith

theorem row2200 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L9619 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L9617 := by
  have h := HLm_submod hΓ [F1] L9618 [F210]
  rw [show [F1] ++ L9618 ++ [F210] = L10717 from rfl, show [F1] ++ L9618 = L10715 from rfl,
    show L9618 ++ [F210] = L10716 from rfl] at h
  rw [i6461 hinj, i6459 hinj, i6460 hinj, i5695 hinj] at h
  linarith

theorem row2201 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L9626 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L9624 := by
  have h := HLm_submod hΓ [F1] L10721 [F210]
  rw [show [F1] ++ L10721 ++ [F210] = L10720 from rfl, show [F1] ++ L10721 = L10718 from rfl,
    show L10721 ++ [F210] = L10719 from rfl] at h
  rw [i6464 hinj, i6462 hinj, i6463 hinj, i6465 hinj] at h
  linarith

theorem row2202 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L9632 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L9630 := by
  have h := HLm_submod hΓ [F1] L10725 [F210]
  rw [show [F1] ++ L10725 ++ [F210] = L10724 from rfl, show [F1] ++ L10725 = L10722 from rfl,
    show L10725 ++ [F210] = L10723 from rfl] at h
  rw [i6468 hinj, i6466 hinj, i6467 hinj, i6469 hinj] at h
  linarith

theorem row2203 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4558 + (1 : ℝ) * HLm Γ 5 L10726 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L9646 := by
  have h := HLm_submod hΓ [F1] L9647 [F67]
  rw [show [F1] ++ L9647 ++ [F67] = L10728 from rfl, show [F1] ++ L9647 = L9648 from rfl,
    show L9647 ++ [F67] = L10727 from rfl] at h
  rw [i6471 hinj, i5716 hinj, i6470 hinj, i5715 hinj] at h
  linarith

theorem row2204 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L9657 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L9655 := by
  have h := HLm_submod hΓ [F1] L10732 [F210]
  rw [show [F1] ++ L10732 ++ [F210] = L10731 from rfl, show [F1] ++ L10732 = L10729 from rfl,
    show L10732 ++ [F210] = L10730 from rfl] at h
  rw [i6474 hinj, i6472 hinj, i6473 hinj, i6475 hinj] at h
  linarith

theorem row2205 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4558 + (1 : ℝ) * HLm Γ 5 L9696 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L8211 := by
  have h := HLm_submod hΓ [F1] L9661 [F67]
  rw [show [F1] ++ L9661 ++ [F67] = L10734 from rfl, show [F1] ++ L9661 = L9662 from rfl,
    show L9661 ++ [F67] = L10733 from rfl] at h
  rw [i6477 hinj, i5727 hinj, i6476 hinj, i5726 hinj] at h
  linarith

theorem row2206 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4558 + (1 : ℝ) * HLm Γ 5 L9667 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L9665 := by
  have h := HLm_submod hΓ [F1] L10738 [F67]
  rw [show [F1] ++ L10738 ++ [F67] = L10737 from rfl, show [F1] ++ L10738 = L10735 from rfl,
    show L10738 ++ [F67] = L10736 from rfl] at h
  rw [i6480 hinj, i6478 hinj, i6479 hinj, i6481 hinj] at h
  linarith

theorem row2207 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L9675 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L9673 := by
  have h := HLm_submod hΓ [F1] L9674 [F210]
  rw [show [F1] ++ L9674 ++ [F210] = L10741 from rfl, show [F1] ++ L9674 = L10739 from rfl,
    show L9674 ++ [F210] = L10740 from rfl] at h
  rw [i6484 hinj, i6482 hinj, i6483 hinj, i5734 hinj] at h
  linarith

theorem row2208 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L9680 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L9678 := by
  have h := HLm_submod hΓ [F1] L10745 [F210]
  rw [show [F1] ++ L10745 ++ [F210] = L10744 from rfl, show [F1] ++ L10745 = L10742 from rfl,
    show L10745 ++ [F210] = L10743 from rfl] at h
  rw [i6487 hinj, i6485 hinj, i6486 hinj, i6488 hinj] at h
  linarith

theorem row2209 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4252 + (1 : ℝ) * HLm Γ 5 L9971 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10749 := by
  have h := HLm_submod hΓ [F1] L10750 [F7]
  rw [show [F1] ++ L10750 ++ [F7] = L10748 from rfl, show [F1] ++ L10750 = L10746 from rfl,
    show L10750 ++ [F7] = L10747 from rfl] at h
  rw [i6491 hinj, i6489 hinj, i6490 hinj, i6492 hinj] at h
  linarith

theorem row2210 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L9729 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L9727 := by
  have h := HLm_submod hΓ [F1] L10754 [F210]
  rw [show [F1] ++ L10754 ++ [F210] = L10753 from rfl, show [F1] ++ L10754 = L10751 from rfl,
    show L10754 ++ [F210] = L10752 from rfl] at h
  rw [i6495 hinj, i6493 hinj, i6494 hinj, i6496 hinj] at h
  linarith

theorem row2211 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L9781 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L9778 := by
  have h := HLm_submod hΓ [F0] L10758 [F210]
  rw [show [F0] ++ L10758 ++ [F210] = L10757 from rfl, show [F0] ++ L10758 = L10755 from rfl,
    show L10758 ++ [F210] = L10756 from rfl] at h
  rw [i6499 hinj, i6497 hinj, i6498 hinj, i6500 hinj] at h
  linarith

theorem row2212 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L9772 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L9768 := by
  have h := HLm_submod hΓ [F0] L10762 [F210]
  rw [show [F0] ++ L10762 ++ [F210] = L10761 from rfl, show [F0] ++ L10762 = L10759 from rfl,
    show L10762 ++ [F210] = L10760 from rfl] at h
  rw [i6503 hinj, i6501 hinj, i6502 hinj, i6504 hinj] at h
  linarith

theorem row2213 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6352 + (1 : ℝ) * HLm Γ 5 L10764 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10767 := by
  have h := HLm_submod hΓ [F0] L10768 [F2]
  rw [show [F0] ++ L10768 ++ [F2] = L10766 from rfl, show [F0] ++ L10768 = L10763 from rfl,
    show L10768 ++ [F2] = L10765 from rfl] at h
  rw [i6507 hinj, i6505 hinj, i6506 hinj, i6508 hinj] at h
  linarith

theorem row2214 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6352 + (1 : ℝ) * HLm Γ 5 L5912 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L9788 := by
  have h := HLm_submod hΓ [F0] L10772 [F2]
  rw [show [F0] ++ L10772 ++ [F2] = L10771 from rfl, show [F0] ++ L10772 = L10769 from rfl,
    show L10772 ++ [F2] = L10770 from rfl] at h
  rw [i6511 hinj, i6509 hinj, i6510 hinj, i6512 hinj] at h
  linarith

theorem row2215 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4558 + (1 : ℝ) * HLm Γ 5 L10773 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L9796 := by
  have h := HLm_submod hΓ [F0] L9797 [F67]
  rw [show [F0] ++ L9797 ++ [F67] = L10775 from rfl, show [F0] ++ L9797 = L9798 from rfl,
    show L9797 ++ [F67] = L10774 from rfl] at h
  rw [i6514 hinj, i5824 hinj, i6513 hinj, i5823 hinj] at h
  linarith

theorem row2216 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L10567 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L9807 := by
  have h := HLm_submod hΓ [F0] L10779 [F210]
  rw [show [F0] ++ L10779 ++ [F210] = L10778 from rfl, show [F0] ++ L10779 = L10776 from rfl,
    show L10779 ++ [F210] = L10777 from rfl] at h
  rw [i6517 hinj, i6515 hinj, i6516 hinj, i6518 hinj] at h
  linarith

theorem row2217 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L9853 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L9849 := by
  have h := HLm_submod hΓ [F0] L10783 [F210]
  rw [show [F0] ++ L10783 ++ [F210] = L10782 from rfl, show [F0] ++ L10783 = L10780 from rfl,
    show L10783 ++ [F210] = L10781 from rfl] at h
  rw [i6521 hinj, i6519 hinj, i6520 hinj, i6522 hinj] at h
  linarith

theorem row2218 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L10785 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10788 := by
  have h := HLm_submod hΓ [F0] L10789 [F210]
  rw [show [F0] ++ L10789 ++ [F210] = L10787 from rfl, show [F0] ++ L10789 = L10784 from rfl,
    show L10789 ++ [F210] = L10786 from rfl] at h
  rw [i6525 hinj, i6523 hinj, i6524 hinj, i6526 hinj] at h
  linarith

theorem row2219 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L9839 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L9836 := by
  have h := HLm_submod hΓ [F0] L10793 [F210]
  rw [show [F0] ++ L10793 ++ [F210] = L10792 from rfl, show [F0] ++ L10793 = L10790 from rfl,
    show L10793 ++ [F210] = L10791 from rfl] at h
  rw [i6529 hinj, i6527 hinj, i6528 hinj, i6530 hinj] at h
  linarith

theorem row2220 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L9846 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L9844 := by
  have h := HLm_submod hΓ [F0] L10797 [F210]
  rw [show [F0] ++ L10797 ++ [F210] = L10796 from rfl, show [F0] ++ L10797 = L10794 from rfl,
    show L10797 ++ [F210] = L10795 from rfl] at h
  rw [i6533 hinj, i6531 hinj, i6532 hinj, i6534 hinj] at h
  linarith

theorem row2221 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L9865 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L9863 := by
  have h := HLm_submod hΓ [F0] L10801 [F210]
  rw [show [F0] ++ L10801 ++ [F210] = L10800 from rfl, show [F0] ++ L10801 = L10798 from rfl,
    show L10801 ++ [F210] = L10799 from rfl] at h
  rw [i6537 hinj, i6535 hinj, i6536 hinj, i6538 hinj] at h
  linarith

theorem row2222 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4558 + (1 : ℝ) * HLm Γ 5 L5724 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L8430 := by
  have h := HLm_submod hΓ [F0] L9868 [F67]
  rw [show [F0] ++ L9868 ++ [F67] = L10803 from rfl, show [F0] ++ L9868 = L9869 from rfl,
    show L9868 ++ [F67] = L10802 from rfl] at h
  rw [i6540 hinj, i5874 hinj, i6539 hinj, i5873 hinj] at h
  linarith

theorem row2223 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L9877 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L9874 := by
  have h := HLm_submod hΓ [F0] L10807 [F210]
  rw [show [F0] ++ L10807 ++ [F210] = L10806 from rfl, show [F0] ++ L10807 = L10804 from rfl,
    show L10807 ++ [F210] = L10805 from rfl] at h
  rw [i6543 hinj, i6541 hinj, i6542 hinj, i6544 hinj] at h
  linarith

theorem row2224 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L9998 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L9995 := by
  have h := HLm_submod hΓ [F0] L10811 [F210]
  rw [show [F0] ++ L10811 ++ [F210] = L10810 from rfl, show [F0] ++ L10811 = L10808 from rfl,
    show L10811 ++ [F210] = L10809 from rfl] at h
  rw [i6547 hinj, i6545 hinj, i6546 hinj, i6548 hinj] at h
  linarith

theorem row2225 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L9883 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L9881 := by
  have h := HLm_submod hΓ [F0] L10815 [F210]
  rw [show [F0] ++ L10815 ++ [F210] = L10814 from rfl, show [F0] ++ L10815 = L10812 from rfl,
    show L10815 ++ [F210] = L10813 from rfl] at h
  rw [i6551 hinj, i6549 hinj, i6550 hinj, i6552 hinj] at h
  linarith

theorem row2226 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L10490 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10486 := by
  have h := HLm_submod hΓ [F0] L10487 [F210]
  rw [show [F0] ++ L10487 ++ [F210] = L10817 from rfl, show [F0] ++ L10487 = L10816 from rfl,
    show L10487 ++ [F210] = L10491 from rfl] at h
  rw [i6554 hinj, i6553 hinj, i6291 hinj, i6289 hinj] at h
  linarith

theorem row2227 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4558 + (1 : ℝ) * HLm Γ 5 L9978 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L9974 := by
  have h := HLm_submod hΓ [F0] L10821 [F67]
  rw [show [F0] ++ L10821 ++ [F67] = L10820 from rfl, show [F0] ++ L10821 = L10818 from rfl,
    show L10821 ++ [F67] = L10819 from rfl] at h
  rw [i6557 hinj, i6555 hinj, i6556 hinj, i6558 hinj] at h
  linarith

theorem row2228 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5931 + (1 : ℝ) * HLm Γ 5 L9906 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L9904 := by
  have h := HLm_submod hΓ [F1] L10825 [F0]
  rw [show [F1] ++ L10825 ++ [F0] = L10824 from rfl, show [F1] ++ L10825 = L10822 from rfl,
    show L10825 ++ [F0] = L10823 from rfl] at h
  rw [i6561 hinj, i6559 hinj, i6560 hinj, i6562 hinj] at h
  linarith

theorem row2229 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9912 + (1 : ℝ) * HLm Γ 5 L5832 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L9910 := by
  have h := HLm_submod hΓ [F1] L9911 [F0]
  rw [show [F1] ++ L9911 ++ [F0] = L10827 from rfl, show [F1] ++ L9911 = L9913 from rfl,
    show L9911 ++ [F0] = L10826 from rfl] at h
  rw [i6564 hinj, i5901 hinj, i6563 hinj, i5900 hinj] at h
  linarith

theorem row2230 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5931 + (1 : ℝ) * HLm Γ 5 L9918 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L9916 := by
  have h := HLm_submod hΓ [F1] L9917 [F0]
  rw [show [F1] ++ L9917 ++ [F0] = L10830 from rfl, show [F1] ++ L9917 = L10828 from rfl,
    show L9917 ++ [F0] = L10829 from rfl] at h
  rw [i6567 hinj, i6565 hinj, i6566 hinj, i5903 hinj] at h
  linarith

theorem row2231 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6520 + (1 : ℝ) * HLm Γ 5 L9965 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L9963 := by
  have h := HLm_submod hΓ [F1] L9964 [F0]
  rw [show [F1] ++ L9964 ++ [F0] = L10833 from rfl, show [F1] ++ L9964 = L10831 from rfl,
    show L9964 ++ [F0] = L10832 from rfl] at h
  rw [i6570 hinj, i6568 hinj, i6569 hinj, i5934 hinj] at h
  linarith

theorem row2232 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5931 + (1 : ℝ) * HLm Γ 5 L5536 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L9989 := by
  have h := HLm_submod hΓ [F1] L10837 [F0]
  rw [show [F1] ++ L10837 ++ [F0] = L10836 from rfl, show [F1] ++ L10837 = L10834 from rfl,
    show L10837 ++ [F0] = L10835 from rfl] at h
  rw [i6573 hinj, i6571 hinj, i6572 hinj, i6574 hinj] at h
  linarith

theorem row2233 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5639 + (1 : ℝ) * HLm Γ 5 L6179 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10025 := by
  have h := HLm_submod hΓ [F1] L10841 [F0]
  rw [show [F1] ++ L10841 ++ [F0] = L10840 from rfl, show [F1] ++ L10841 = L10838 from rfl,
    show L10841 ++ [F0] = L10839 from rfl] at h
  rw [i6577 hinj, i6575 hinj, i6576 hinj, i6578 hinj] at h
  linarith

theorem row2234 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L10047 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10045 := by
  have h := HLm_submod hΓ [F0] L10046 [F210]
  rw [show [F0] ++ L10046 ++ [F210] = L10844 from rfl, show [F0] ++ L10046 = L10842 from rfl,
    show L10046 ++ [F210] = L10843 from rfl] at h
  rw [i6581 hinj, i6579 hinj, i6580 hinj, i5996 hinj] at h
  linarith

theorem row2235 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L10142 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10138 := by
  have h := HLm_submod hΓ [F0] L10848 [F210]
  rw [show [F0] ++ L10848 ++ [F210] = L10847 from rfl, show [F0] ++ L10848 = L10845 from rfl,
    show L10848 ++ [F210] = L10846 from rfl] at h
  rw [i6584 hinj, i6582 hinj, i6583 hinj, i6585 hinj] at h
  linarith

theorem row2236 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L10059 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10057 := by
  have h := HLm_submod hΓ [F0] L10058 [F210]
  rw [show [F0] ++ L10058 ++ [F210] = L10851 from rfl, show [F0] ++ L10058 = L10849 from rfl,
    show L10058 ++ [F210] = L10850 from rfl] at h
  rw [i6588 hinj, i6586 hinj, i6587 hinj, i6004 hinj] at h
  linarith

theorem row2237 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L10067 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10065 := by
  have h := HLm_submod hΓ [F0] L10066 [F210]
  rw [show [F0] ++ L10066 ++ [F210] = L10854 from rfl, show [F0] ++ L10066 = L10852 from rfl,
    show L10066 ++ [F210] = L10853 from rfl] at h
  rw [i6591 hinj, i6589 hinj, i6590 hinj, i6008 hinj] at h
  linarith

theorem row2238 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L10074 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10071 := by
  have h := HLm_submod hΓ [F0] L10858 [F210]
  rw [show [F0] ++ L10858 ++ [F210] = L10857 from rfl, show [F0] ++ L10858 = L10855 from rfl,
    show L10858 ++ [F210] = L10856 from rfl] at h
  rw [i6594 hinj, i6592 hinj, i6593 hinj, i6595 hinj] at h
  linarith

theorem row2239 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L10122 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10119 := by
  have h := HLm_submod hΓ [F0] L10862 [F210]
  rw [show [F0] ++ L10862 ++ [F210] = L10861 from rfl, show [F0] ++ L10862 = L10859 from rfl,
    show L10862 ++ [F210] = L10860 from rfl] at h
  rw [i6598 hinj, i6596 hinj, i6597 hinj, i6599 hinj] at h
  linarith

theorem row2240 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L10103 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10101 := by
  have h := HLm_submod hΓ [F0] L10866 [F210]
  rw [show [F0] ++ L10866 ++ [F210] = L10865 from rfl, show [F0] ++ L10866 = L10863 from rfl,
    show L10866 ++ [F210] = L10864 from rfl] at h
  rw [i6602 hinj, i6600 hinj, i6601 hinj, i6603 hinj] at h
  linarith

theorem row2241 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L10081 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10079 := by
  have h := HLm_submod hΓ [F0] L10080 [F210]
  rw [show [F0] ++ L10080 ++ [F210] = L10869 from rfl, show [F0] ++ L10080 = L10867 from rfl,
    show L10080 ++ [F210] = L10868 from rfl] at h
  rw [i6606 hinj, i6604 hinj, i6605 hinj, i6016 hinj] at h
  linarith

theorem row2242 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5489 + (1 : ℝ) * HLm Γ 5 L10764 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10873 := by
  have h := HLm_submod hΓ [F0] L10874 [F1]
  rw [show [F0] ++ L10874 ++ [F1] = L10872 from rfl, show [F0] ++ L10874 = L10870 from rfl,
    show L10874 ++ [F1] = L10871 from rfl] at h
  rw [i6609 hinj, i6607 hinj, i6608 hinj, i6610 hinj] at h
  linarith

theorem row2243 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L6522 + (1 : ℝ) * HLm Γ 5 L10876 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10879 := by
  have h := HLm_submod hΓ [F0] L10880 [F1]
  rw [show [F0] ++ L10880 ++ [F1] = L10878 from rfl, show [F0] ++ L10880 = L10875 from rfl,
    show L10880 ++ [F1] = L10877 from rfl] at h
  rw [i6613 hinj, i6611 hinj, i6612 hinj, i6614 hinj] at h
  linarith

theorem row2244 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L10129 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10127 := by
  have h := HLm_submod hΓ [F0] L10884 [F210]
  rw [show [F0] ++ L10884 ++ [F210] = L10883 from rfl, show [F0] ++ L10884 = L10881 from rfl,
    show L10884 ++ [F210] = L10882 from rfl] at h
  rw [i6617 hinj, i6615 hinj, i6616 hinj, i6618 hinj] at h
  linarith

theorem row2245 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4558 + (1 : ℝ) * HLm Γ 5 L10223 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10888 := by
  have h := HLm_submod hΓ [F0] L10889 [F67]
  rw [show [F0] ++ L10889 ++ [F67] = L10887 from rfl, show [F0] ++ L10889 = L10885 from rfl,
    show L10889 ++ [F67] = L10886 from rfl] at h
  rw [i6621 hinj, i6619 hinj, i6620 hinj, i6622 hinj] at h
  linarith

theorem row2246 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L10345 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10144 := by
  have h := HLm_submod hΓ [F0] L10893 [F210]
  rw [show [F0] ++ L10893 ++ [F210] = L10892 from rfl, show [F0] ++ L10893 = L10890 from rfl,
    show L10893 ++ [F210] = L10891 from rfl] at h
  rw [i6625 hinj, i6623 hinj, i6624 hinj, i6626 hinj] at h
  linarith

theorem row2247 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L10895 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10898 := by
  have h := HLm_submod hΓ [F0] L10899 [F210]
  rw [show [F0] ++ L10899 ++ [F210] = L10897 from rfl, show [F0] ++ L10899 = L10894 from rfl,
    show L10899 ++ [F210] = L10896 from rfl] at h
  rw [i6629 hinj, i6627 hinj, i6628 hinj, i6630 hinj] at h
  linarith

theorem row2248 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L10155 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10153 := by
  have h := HLm_submod hΓ [F0] L10903 [F210]
  rw [show [F0] ++ L10903 ++ [F210] = L10902 from rfl, show [F0] ++ L10903 = L10900 from rfl,
    show L10903 ++ [F210] = L10901 from rfl] at h
  rw [i6633 hinj, i6631 hinj, i6632 hinj, i6634 hinj] at h
  linarith

theorem row2249 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L10905 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L10908 := by
  have h := HLm_submod hΓ [F0] L10909 [F210]
  rw [show [F0] ++ L10909 ++ [F210] = L10907 from rfl, show [F0] ++ L10909 = L10904 from rfl,
    show L10909 ++ [F210] = L10906 from rfl] at h
  rw [i6637 hinj, i6635 hinj, i6636 hinj, i6638 hinj] at h
  linarith

end EntropyBounds.TwoSet.Certs.R7A5
