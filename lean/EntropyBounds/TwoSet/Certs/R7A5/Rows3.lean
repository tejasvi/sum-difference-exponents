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

theorem row450 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2141 + (1 : ℝ) * HLm Γ 5 L2143 + (-1 : ℝ) * HLm Γ 5 L2145 + (-1 : ℝ) * HLm Γ 5 L427 := by
  have h := HLm_submod hΓ [F67] L428 [F90]
  rw [show [F67] ++ L428 ++ [F90] = L2146 from rfl, show [F67] ++ L428 = L2142 from rfl,
    show L428 ++ [F90] = L2144 from rfl] at h
  rw [i1176 hinj, i1174 hinj, i1175 hinj, i174 hinj] at h
  linarith

theorem row451 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2147 + (1 : ℝ) * HLm Γ 5 L2149 + (-1 : ℝ) * HLm Γ 5 L2151 + (-1 : ℝ) * HLm Γ 5 L427 := by
  have h := HLm_submod hΓ [F52] L428 [F25]
  rw [show [F52] ++ L428 ++ [F25] = L2152 from rfl, show [F52] ++ L428 = L2148 from rfl,
    show L428 ++ [F25] = L2150 from rfl] at h
  rw [i1179 hinj, i1177 hinj, i1178 hinj, i174 hinj] at h
  linarith

theorem row452 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L217 + (1 : ℝ) * HLm Γ 5 L2153 + (-1 : ℝ) * HLm Γ 5 L2155 + (-1 : ℝ) * HLm Γ 5 L456 := by
  have h := HLm_submod hΓ [F16] L456 [F41]
  rw [show [F16] ++ L456 ++ [F41] = L2156 from rfl, show [F16] ++ L456 = L451 from rfl,
    show L456 ++ [F41] = L2154 from rfl] at h
  rw [i1181 hinj, i186 hinj, i1180 hinj] at h
  linarith

theorem row453 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L616 + (1 : ℝ) * HLm Γ 5 L2157 + (-1 : ℝ) * HLm Γ 5 L2158 + (-1 : ℝ) * HLm Γ 5 L60 := by
  have h := HLm_submod hΓ [F1] L60 [F22]
  rw [show [F1] ++ L60 ++ [F22] = L2159 from rfl, show [F1] ++ L60 = L617 from rfl,
    show L60 ++ [F22] = L2157 from rfl] at h
  rw [i1182 hinj, i264 hinj] at h
  linarith

theorem row454 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2160 + (1 : ℝ) * HLm Γ 5 L431 + (-1 : ℝ) * HLm Γ 5 L2163 + (-1 : ℝ) * HLm Γ 5 L60 := by
  have h := HLm_submod hΓ [F2] L60 [F85]
  rw [show [F2] ++ L60 ++ [F85] = L2164 from rfl, show [F2] ++ L60 = L2161 from rfl,
    show L60 ++ [F85] = L2162 from rfl] at h
  rw [i1185 hinj, i1183 hinj, i1184 hinj] at h
  linarith

theorem row455 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2165 + (1 : ℝ) * HLm Γ 5 L952 + (-1 : ℝ) * HLm Γ 5 L2168 + (-1 : ℝ) * HLm Γ 5 L2170 := by
  have h := HLm_submod hΓ [F3] L2170 [F16]
  rw [show [F3] ++ L2170 ++ [F16] = L2169 from rfl, show [F3] ++ L2170 = L2166 from rfl,
    show L2170 ++ [F16] = L2167 from rfl] at h
  rw [i1188 hinj, i1186 hinj, i1187 hinj] at h
  linarith

theorem row456 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L114 + (1 : ℝ) * HLm Γ 5 L1983 + (-1 : ℝ) * HLm Γ 5 L1223 + (-1 : ℝ) * HLm Γ 5 L503 := by
  have h := HLm_submod hΓ [F7] L503 [F31]
  rw [show [F7] ++ L503 ++ [F31] = L2173 from rfl, show [F7] ++ L503 = L2171 from rfl,
    show L503 ++ [F31] = L2172 from rfl] at h
  rw [i1191 hinj, i1189 hinj, i1190 hinj] at h
  linarith

theorem row457 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2174 + (1 : ℝ) * HLm Γ 5 L2176 + (-1 : ℝ) * HLm Γ 5 L644 + (-1 : ℝ) * HLm Γ 5 L19 := by
  have h := HLm_submod hΓ [F16] L19 [F19]
  rw [show [F16] ++ L19 ++ [F19] = L2177 from rfl, show [F16] ++ L19 = L2175 from rfl,
    show L19 ++ [F19] = L2176 from rfl] at h
  rw [i1193 hinj, i1192 hinj] at h
  linarith

theorem row458 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2178 + (1 : ℝ) * HLm Γ 5 L1979 + (-1 : ℝ) * HLm Γ 5 L2181 + (-1 : ℝ) * HLm Γ 5 L549 := by
  have h := HLm_submod hΓ [F62] L549 [F33]
  rw [show [F62] ++ L549 ++ [F33] = L2182 from rfl, show [F62] ++ L549 = L2179 from rfl,
    show L549 ++ [F33] = L2180 from rfl] at h
  rw [i1196 hinj, i1194 hinj, i1195 hinj] at h
  linarith

theorem row459 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2085 + (1 : ℝ) * HLm Γ 5 L2184 + (-1 : ℝ) * HLm Γ 5 L2186 + (-1 : ℝ) * HLm Γ 5 L549 := by
  have h := HLm_submod hΓ [F23] L549 [F27]
  rw [show [F23] ++ L549 ++ [F27] = L2187 from rfl, show [F23] ++ L549 = L2183 from rfl,
    show L549 ++ [F27] = L2185 from rfl] at h
  rw [i1199 hinj, i1197 hinj, i1198 hinj] at h
  linarith

theorem row460 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L258 + (1 : ℝ) * HLm Γ 5 L2072 + (-1 : ℝ) * HLm Γ 5 L2189 + (-1 : ℝ) * HLm Γ 5 L252 := by
  have h := HLm_submod hΓ [F1] L252 [F48]
  rw [show [F1] ++ L252 ++ [F48] = L2190 from rfl, show [F1] ++ L252 = L2188 from rfl,
    show L252 ++ [F48] = L2072 from rfl] at h
  rw [i1201 hinj, i1200 hinj] at h
  linarith

theorem row461 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2191 + (1 : ℝ) * HLm Γ 5 L550 + (-1 : ℝ) * HLm Γ 5 L2193 + (-1 : ℝ) * HLm Γ 5 L252 := by
  have h := HLm_submod hΓ [F3] L252 [F16]
  rw [show [F3] ++ L252 ++ [F16] = L2194 from rfl, show [F3] ++ L252 = L2192 from rfl,
    show L252 ++ [F16] = L550 from rfl] at h
  rw [i1203 hinj, i1202 hinj] at h
  linarith

theorem row462 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L9 + (1 : ℝ) * HLm Γ 5 L1986 + (-1 : ℝ) * HLm Γ 5 L2197 + (-1 : ℝ) * HLm Γ 5 L6 := by
  have h := HLm_submod hΓ [F1] L6 [F13]
  rw [show [F1] ++ L6 ++ [F13] = L2198 from rfl, show [F1] ++ L6 = L2195 from rfl,
    show L6 ++ [F13] = L2196 from rfl] at h
  rw [i1206 hinj, i1204 hinj, i1205 hinj] at h
  linarith

theorem row463 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L565 + (1 : ℝ) * HLm Γ 5 L2039 + (-1 : ℝ) * HLm Γ 5 L731 + (-1 : ℝ) * HLm Γ 5 L99 := by
  have h := HLm_submod hΓ [F1] L99 [F13]
  rw [show [F1] ++ L99 ++ [F13] = L2199 from rfl, show [F1] ++ L99 = L566 from rfl,
    show L99 ++ [F13] = L2040 from rfl] at h
  rw [i1207 hinj, i237 hinj, i1117 hinj] at h
  linarith

theorem row464 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2200 + (1 : ℝ) * HLm Γ 5 L2202 + (-1 : ℝ) * HLm Γ 5 L2204 + (-1 : ℝ) * HLm Γ 5 L99 := by
  have h := HLm_submod hΓ [F16] L99 [F117]
  rw [show [F16] ++ L99 ++ [F117] = L2205 from rfl, show [F16] ++ L99 = L2201 from rfl,
    show L99 ++ [F117] = L2203 from rfl] at h
  rw [i1210 hinj, i1208 hinj, i1209 hinj] at h
  linarith

theorem row465 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L89 + (1 : ℝ) * HLm Γ 5 L2206 + (-1 : ℝ) * HLm Γ 5 L638 + (-1 : ℝ) * HLm Γ 5 L12 := by
  have h := HLm_submod hΓ [F7] L12 [F1]
  rw [show [F7] ++ L12 ++ [F1] = L2208 from rfl, show [F7] ++ L12 = L90 from rfl,
    show L12 ++ [F1] = L2207 from rfl] at h
  rw [i1212 hinj, i22 hinj, i1211 hinj] at h
  linarith

theorem row466 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L565 + (1 : ℝ) * HLm Γ 5 L582 + (-1 : ℝ) * HLm Γ 5 L568 + (-1 : ℝ) * HLm Γ 5 L288 := by
  have h := HLm_submod hΓ [F1] L288 [F48]
  rw [show [F1] ++ L288 ++ [F48] = L1347 from rfl, show [F1] ++ L288 = L2209 from rfl,
    show L288 ++ [F48] = L582 from rfl] at h
  rw [i666 hinj, i1213 hinj] at h
  linarith

theorem row467 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2210 + (1 : ℝ) * HLm Γ 5 L2212 + (-1 : ℝ) * HLm Γ 5 L2214 + (-1 : ℝ) * HLm Γ 5 L393 := by
  have h := HLm_submod hΓ [F67] L393 [F25]
  rw [show [F67] ++ L393 ++ [F25] = L2215 from rfl, show [F67] ++ L393 = L2211 from rfl,
    show L393 ++ [F25] = L2213 from rfl] at h
  rw [i1216 hinj, i1214 hinj, i1215 hinj] at h
  linarith

theorem row468 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2216 + (1 : ℝ) * HLm Γ 5 L106 + (-1 : ℝ) * HLm Γ 5 L2219 + (-1 : ℝ) * HLm Γ 5 L14 := by
  have h := HLm_submod hΓ [F62] L14 [F16]
  rw [show [F62] ++ L14 ++ [F16] = L2220 from rfl, show [F62] ++ L14 = L2217 from rfl,
    show L14 ++ [F16] = L2218 from rfl] at h
  rw [i1219 hinj, i1217 hinj, i1218 hinj] at h
  linarith

theorem row469 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L679 + (1 : ℝ) * HLm Γ 5 L502 + (-1 : ℝ) * HLm Γ 5 L839 + (-1 : ℝ) * HLm Γ 5 L500 := by
  have h := HLm_submod hΓ [F7] L500 [F3]
  rw [show [F7] ++ L500 ++ [F3] = L2222 from rfl, show [F7] ++ L500 = L2221 from rfl,
    show L500 ++ [F3] = L502 from rfl] at h
  rw [i1221 hinj, i1220 hinj] at h
  linarith

theorem row470 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2223 + (1 : ℝ) * HLm Γ 5 L2225 + (-1 : ℝ) * HLm Γ 5 L2227 + (-1 : ℝ) * HLm Γ 5 L544 := by
  have h := HLm_submod hΓ [F23] L544 [F43]
  rw [show [F23] ++ L544 ++ [F43] = L2228 from rfl, show [F23] ++ L544 = L2224 from rfl,
    show L544 ++ [F43] = L2226 from rfl] at h
  rw [i1224 hinj, i1222 hinj, i1223 hinj] at h
  linarith

theorem row471 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L707 + (1 : ℝ) * HLm Γ 5 L2230 + (-1 : ℝ) * HLm Γ 5 L2232 + (-1 : ℝ) * HLm Γ 5 L2001 := by
  have h := HLm_submod hΓ [F2] L2002 [F43]
  rw [show [F2] ++ L2002 ++ [F43] = L2233 from rfl, show [F2] ++ L2002 = L2229 from rfl,
    show L2002 ++ [F43] = L2231 from rfl] at h
  rw [i1227 hinj, i1225 hinj, i1226 hinj, i1097 hinj] at h
  linarith

theorem row472 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2234 + (1 : ℝ) * HLm Γ 5 L2236 + (-1 : ℝ) * HLm Γ 5 L2238 + (-1 : ℝ) * HLm Γ 5 L2001 := by
  have h := HLm_submod hΓ [F16] L2002 [F19]
  rw [show [F16] ++ L2002 ++ [F19] = L2239 from rfl, show [F16] ++ L2002 = L2235 from rfl,
    show L2002 ++ [F19] = L2237 from rfl] at h
  rw [i1230 hinj, i1228 hinj, i1229 hinj, i1097 hinj] at h
  linarith

theorem row473 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L576 + (1 : ℝ) * HLm Γ 5 L305 + (-1 : ℝ) * HLm Γ 5 L2241 + (-1 : ℝ) * HLm Γ 5 L303 := by
  have h := HLm_submod hΓ [F0] L635 [F23]
  rw [show [F0] ++ L635 ++ [F23] = L2242 from rfl, show [F0] ++ L635 = L2240 from rfl,
    show L635 ++ [F23] = L2050 from rfl] at h
  rw [i1232 hinj, i1231 hinj, i1124 hinj, i273 hinj] at h
  linarith

theorem row474 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L157 + (1 : ℝ) * HLm Γ 5 L2244 + (-1 : ℝ) * HLm Γ 5 L2246 + (-1 : ℝ) * HLm Γ 5 L660 := by
  have h := HLm_submod hΓ [F0] L661 [F43]
  rw [show [F0] ++ L661 ++ [F43] = L2247 from rfl, show [F0] ++ L661 = L2243 from rfl,
    show L661 ++ [F43] = L2245 from rfl] at h
  rw [i1235 hinj, i1233 hinj, i1234 hinj, i286 hinj] at h
  linarith

theorem row475 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1215 + (1 : ℝ) * HLm Γ 5 L1990 + (-1 : ℝ) * HLm Γ 5 L2250 + (-1 : ℝ) * HLm Γ 5 L120 := by
  have h := HLm_submod hΓ [F16] L120 [F59]
  rw [show [F16] ++ L120 ++ [F59] = L2251 from rfl, show [F16] ++ L120 = L2248 from rfl,
    show L120 ++ [F59] = L2249 from rfl] at h
  rw [i1238 hinj, i1236 hinj, i1237 hinj] at h
  linarith

theorem row476 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L849 + (1 : ℝ) * HLm Γ 5 L671 + (-1 : ℝ) * HLm Γ 5 L825 + (-1 : ℝ) * HLm Γ 5 L677 := by
  have h := HLm_submod hΓ [F0] L678 [F2]
  rw [show [F0] ++ L678 ++ [F2] = L2254 from rfl, show [F0] ++ L678 = L2252 from rfl,
    show L678 ++ [F2] = L2253 from rfl] at h
  rw [i1241 hinj, i1239 hinj, i1240 hinj, i294 hinj] at h
  linarith

theorem row477 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L673 + (1 : ℝ) * HLm Γ 5 L1992 + (-1 : ℝ) * HLm Γ 5 L2257 + (-1 : ℝ) * HLm Γ 5 L677 := by
  have h := HLm_submod hΓ [F16] L678 [F59]
  rw [show [F16] ++ L678 ++ [F59] = L2258 from rfl, show [F16] ++ L678 = L2255 from rfl,
    show L678 ++ [F59] = L2256 from rfl] at h
  rw [i1244 hinj, i1242 hinj, i1243 hinj, i294 hinj] at h
  linarith

theorem row478 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L92 + (1 : ℝ) * HLm Γ 5 L1223 + (-1 : ℝ) * HLm Γ 5 L842 + (-1 : ℝ) * HLm Γ 5 L1994 := by
  have h := HLm_submod hΓ [F0] L2262 [F6]
  rw [show [F0] ++ L2262 ++ [F6] = L2261 from rfl, show [F0] ++ L2262 = L2259 from rfl,
    show L2262 ++ [F6] = L2260 from rfl] at h
  rw [i1247 hinj, i1245 hinj, i1246 hinj, i1248 hinj] at h
  linarith

theorem row479 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L679 + (1 : ℝ) * HLm Γ 5 L2263 + (-1 : ℝ) * HLm Γ 5 L842 + (-1 : ℝ) * HLm Γ 5 L532 := by
  have h := HLm_submod hΓ [F0] L685 [F43]
  rw [show [F0] ++ L685 ++ [F43] = L2265 from rfl, show [F0] ++ L685 = L680 from rfl,
    show L685 ++ [F43] = L2264 from rfl] at h
  rw [i1250 hinj, i295 hinj, i1249 hinj, i298 hinj] at h
  linarith

theorem row480 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2266 + (1 : ℝ) * HLm Γ 5 L2268 + (-1 : ℝ) * HLm Γ 5 L2270 + (-1 : ℝ) * HLm Γ 5 L1988 := by
  have h := HLm_submod hΓ [F51] L1989 [F45]
  rw [show [F51] ++ L1989 ++ [F45] = L2271 from rfl, show [F51] ++ L1989 = L2267 from rfl,
    show L1989 ++ [F45] = L2269 from rfl] at h
  rw [i1253 hinj, i1251 hinj, i1252 hinj, i1091 hinj] at h
  linarith

theorem row481 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2272 + (1 : ℝ) * HLm Γ 5 L2274 + (-1 : ℝ) * HLm Γ 5 L2276 + (-1 : ℝ) * HLm Γ 5 L2130 := by
  have h := HLm_submod hΓ [F0] L2131 [F82]
  rw [show [F0] ++ L2131 ++ [F82] = L2277 from rfl, show [F0] ++ L2131 = L2273 from rfl,
    show L2131 ++ [F82] = L2275 from rfl] at h
  rw [i1256 hinj, i1254 hinj, i1255 hinj, i1167 hinj] at h
  linarith

theorem row482 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2278 + (1 : ℝ) * HLm Γ 5 L2280 + (-1 : ℝ) * HLm Γ 5 L2282 + (-1 : ℝ) * HLm Γ 5 L2284 := by
  have h := HLm_submod hΓ [F68] L2285 [F59]
  rw [show [F68] ++ L2285 ++ [F59] = L2283 from rfl, show [F68] ++ L2285 = L2279 from rfl,
    show L2285 ++ [F59] = L2281 from rfl] at h
  rw [i1259 hinj, i1257 hinj, i1258 hinj, i1260 hinj] at h
  linarith

theorem row483 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2286 + (1 : ℝ) * HLm Γ 5 L714 + (-1 : ℝ) * HLm Γ 5 L2288 + (-1 : ℝ) * HLm Γ 5 L717 := by
  have h := HLm_submod hΓ [F0] L717 [F67]
  rw [show [F0] ++ L717 ++ [F67] = L2289 from rfl, show [F0] ++ L717 = L2287 from rfl,
    show L717 ++ [F67] = L714 from rfl] at h
  rw [i1262 hinj, i1261 hinj] at h
  linarith

theorem row484 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2290 + (1 : ℝ) * HLm Γ 5 L2008 + (-1 : ℝ) * HLm Γ 5 L2293 + (-1 : ℝ) * HLm Γ 5 L2006 := by
  have h := HLm_submod hΓ [F9] L2007 [F45]
  rw [show [F9] ++ L2007 ++ [F45] = L2294 from rfl, show [F9] ++ L2007 = L2291 from rfl,
    show L2007 ++ [F45] = L2292 from rfl] at h
  rw [i1265 hinj, i1263 hinj, i1264 hinj, i1099 hinj] at h
  linarith

theorem row485 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2016 + (1 : ℝ) * HLm Γ 5 L2296 + (-1 : ℝ) * HLm Γ 5 L2298 + (-1 : ℝ) * HLm Γ 5 L2014 := by
  have h := HLm_submod hΓ [F22] L2014 [F23]
  rw [show [F22] ++ L2014 ++ [F23] = L2299 from rfl, show [F22] ++ L2014 = L2295 from rfl,
    show L2014 ++ [F23] = L2297 from rfl] at h
  rw [i1268 hinj, i1266 hinj, i1267 hinj] at h
  linarith

theorem row486 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1960 + (1 : ℝ) * HLm Γ 5 L2301 + (-1 : ℝ) * HLm Γ 5 L2303 + (-1 : ℝ) * HLm Γ 5 L2305 := by
  have h := HLm_submod hΓ [F0] L2305 [F20]
  rw [show [F0] ++ L2305 ++ [F20] = L2304 from rfl, show [F0] ++ L2305 = L2300 from rfl,
    show L2305 ++ [F20] = L2302 from rfl] at h
  rw [i1271 hinj, i1269 hinj, i1270 hinj] at h
  linarith

theorem row487 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2306 + (1 : ℝ) * HLm Γ 5 L2308 + (-1 : ℝ) * HLm Γ 5 L2310 + (-1 : ℝ) * HLm Γ 5 L2305 := by
  have h := HLm_submod hΓ [F1] L2305 [F52]
  rw [show [F1] ++ L2305 ++ [F52] = L2311 from rfl, show [F1] ++ L2305 = L2307 from rfl,
    show L2305 ++ [F52] = L2309 from rfl] at h
  rw [i1274 hinj, i1272 hinj, i1273 hinj] at h
  linarith

theorem row488 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2312 + (1 : ℝ) * HLm Γ 5 L2314 + (-1 : ℝ) * HLm Γ 5 L2315 + (-1 : ℝ) * HLm Γ 5 L2305 := by
  have h := HLm_submod hΓ [F51] L2305 [F67]
  rw [show [F51] ++ L2305 ++ [F67] = L2316 from rfl, show [F51] ++ L2305 = L2313 from rfl,
    show L2305 ++ [F67] = L2314 from rfl] at h
  rw [i1276 hinj, i1275 hinj] at h
  linarith

theorem row489 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L776 + (1 : ℝ) * HLm Γ 5 L2318 + (-1 : ℝ) * HLm Γ 5 L1606 + (-1 : ℝ) * HLm Γ 5 L172 := by
  have h := HLm_submod hΓ [F16] L780 [F67]
  rw [show [F16] ++ L780 ++ [F67] = L2320 from rfl, show [F16] ++ L780 = L2317 from rfl,
    show L780 ++ [F67] = L2319 from rfl] at h
  rw [i1279 hinj, i1277 hinj, i1278 hinj, i347 hinj] at h
  linarith

theorem row490 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2321 + (1 : ℝ) * HLm Γ 5 L2323 + (-1 : ℝ) * HLm Γ 5 L2325 + (-1 : ℝ) * HLm Γ 5 L2327 := by
  have h := HLm_submod hΓ [F67] L2328 [F25]
  rw [show [F67] ++ L2328 ++ [F25] = L2326 from rfl, show [F67] ++ L2328 = L2322 from rfl,
    show L2328 ++ [F25] = L2324 from rfl] at h
  rw [i1282 hinj, i1280 hinj, i1281 hinj, i1283 hinj] at h
  linarith

theorem row491 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L157 + (1 : ℝ) * HLm Γ 5 L2329 + (-1 : ℝ) * HLm Γ 5 L588 + (-1 : ℝ) * HLm Γ 5 L155 := by
  have h := HLm_submod hΓ [F0] L156 [F82]
  rw [show [F0] ++ L156 ++ [F82] = L2331 from rfl, show [F0] ++ L156 = L158 from rfl,
    show L156 ++ [F82] = L2330 from rfl] at h
  rw [i1285 hinj, i51 hinj, i1284 hinj, i50 hinj] at h
  linarith

theorem row492 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2018 + (1 : ℝ) * HLm Γ 5 L2332 + (-1 : ℝ) * HLm Γ 5 L2334 + (-1 : ℝ) * HLm Γ 5 L174 := by
  have h := HLm_submod hΓ [F3] L175 [F22]
  rw [show [F3] ++ L175 ++ [F22] = L2335 from rfl, show [F3] ++ L175 = L2019 from rfl,
    show L175 ++ [F22] = L2333 from rfl] at h
  rw [i1287 hinj, i1105 hinj, i1286 hinj, i59 hinj] at h
  linarith

theorem row493 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L679 + (1 : ℝ) * HLm Γ 5 L2336 + (-1 : ℝ) * HLm Γ 5 L2338 + (-1 : ℝ) * HLm Γ 5 L827 := by
  have h := HLm_submod hΓ [F0] L827 [F108]
  rw [show [F0] ++ L827 ++ [F108] = L2339 from rfl, show [F0] ++ L827 = L822 from rfl,
    show L827 ++ [F108] = L2337 from rfl] at h
  rw [i1289 hinj, i370 hinj, i1288 hinj] at h
  linarith

theorem row494 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L29 + (1 : ℝ) * HLm Γ 5 L2341 + (-1 : ℝ) * HLm Γ 5 L2343 + (-1 : ℝ) * HLm Γ 5 L2345 := by
  have h := HLm_submod hΓ [F0] L2345 [F55]
  rw [show [F0] ++ L2345 ++ [F55] = L2344 from rfl, show [F0] ++ L2345 = L2340 from rfl,
    show L2345 ++ [F55] = L2342 from rfl] at h
  rw [i1292 hinj, i1290 hinj, i1291 hinj] at h
  linarith

theorem row495 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L854 + (1 : ℝ) * HLm Γ 5 L188 + (-1 : ℝ) * HLm Γ 5 L2346 + (-1 : ℝ) * HLm Γ 5 L183 := by
  have h := HLm_submod hΓ [F0] L183 [F45]
  rw [show [F0] ++ L183 ++ [F45] = L2347 from rfl, show [F0] ++ L183 = L855 from rfl,
    show L183 ++ [F45] = L188 from rfl] at h
  rw [i1293 hinj, i389 hinj] at h
  linarith

theorem row496 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2348 + (1 : ℝ) * HLm Γ 5 L2350 + (-1 : ℝ) * HLm Γ 5 L2352 + (-1 : ℝ) * HLm Γ 5 L2354 := by
  have h := HLm_submod hΓ [F0] L2355 [F67]
  rw [show [F0] ++ L2355 ++ [F67] = L2353 from rfl, show [F0] ++ L2355 = L2349 from rfl,
    show L2355 ++ [F67] = L2351 from rfl] at h
  rw [i1296 hinj, i1294 hinj, i1295 hinj, i1297 hinj] at h
  linarith

theorem row497 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2356 + (1 : ℝ) * HLm Γ 5 L2358 + (-1 : ℝ) * HLm Γ 5 L2360 + (-1 : ℝ) * HLm Γ 5 L2362 := by
  have h := HLm_submod hΓ [F16] L2362 [F52]
  rw [show [F16] ++ L2362 ++ [F52] = L2361 from rfl, show [F16] ++ L2362 = L2357 from rfl,
    show L2362 ++ [F52] = L2359 from rfl] at h
  rw [i1300 hinj, i1298 hinj, i1299 hinj] at h
  linarith

theorem row498 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L866 + (1 : ℝ) * HLm Γ 5 L2364 + (-1 : ℝ) * HLm Γ 5 L870 + (-1 : ℝ) * HLm Γ 5 L878 := by
  have h := HLm_submod hΓ [F7] L878 [F23]
  rw [show [F7] ++ L878 ++ [F23] = L2366 from rfl, show [F7] ++ L878 = L2363 from rfl,
    show L878 ++ [F23] = L2365 from rfl] at h
  rw [i1303 hinj, i1301 hinj, i1302 hinj] at h
  linarith

theorem row499 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2367 + (1 : ℝ) * HLm Γ 5 L883 + (-1 : ℝ) * HLm Γ 5 L2370 + (-1 : ℝ) * HLm Γ 5 L889 := by
  have h := HLm_submod hΓ [F47] L890 [F67]
  rw [show [F47] ++ L890 ++ [F67] = L2371 from rfl, show [F47] ++ L890 = L2368 from rfl,
    show L890 ++ [F67] = L2369 from rfl] at h
  rw [i1306 hinj, i1304 hinj, i1305 hinj, i405 hinj] at h
  linarith

theorem row500 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2372 + (1 : ℝ) * HLm Γ 5 L2374 + (-1 : ℝ) * HLm Γ 5 L2376 + (-1 : ℝ) * HLm Γ 5 L2378 := by
  have h := HLm_submod hΓ [F47] L2378 [F16]
  rw [show [F47] ++ L2378 ++ [F16] = L2377 from rfl, show [F47] ++ L2378 = L2373 from rfl,
    show L2378 ++ [F16] = L2375 from rfl] at h
  rw [i1309 hinj, i1307 hinj, i1308 hinj] at h
  linarith

theorem row501 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2379 + (1 : ℝ) * HLm Γ 5 L2181 + (-1 : ℝ) * HLm Γ 5 L2382 + (-1 : ℝ) * HLm Γ 5 L2109 := by
  have h := HLm_submod hΓ [F2] L2110 [F67]
  rw [show [F2] ++ L2110 ++ [F67] = L2383 from rfl, show [F2] ++ L2110 = L2380 from rfl,
    show L2110 ++ [F67] = L2381 from rfl] at h
  rw [i1312 hinj, i1310 hinj, i1311 hinj, i1157 hinj] at h
  linarith

theorem row502 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2384 + (1 : ℝ) * HLm Γ 5 L2386 + (-1 : ℝ) * HLm Γ 5 L2388 + (-1 : ℝ) * HLm Γ 5 L2078 := by
  have h := HLm_submod hΓ [F47] L2079 [F48]
  rw [show [F47] ++ L2079 ++ [F48] = L2389 from rfl, show [F47] ++ L2079 = L2385 from rfl,
    show L2079 ++ [F48] = L2387 from rfl] at h
  rw [i1315 hinj, i1313 hinj, i1314 hinj, i1140 hinj] at h
  linarith

theorem row503 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2390 + (1 : ℝ) * HLm Γ 5 L2391 + (-1 : ℝ) * HLm Γ 5 L2393 + (-1 : ℝ) * HLm Γ 5 L2395 := by
  have h := HLm_submod hΓ [F47] L2395 [F16]
  rw [show [F47] ++ L2395 ++ [F16] = L2394 from rfl, show [F47] ++ L2395 = L2390 from rfl,
    show L2395 ++ [F16] = L2392 from rfl] at h
  rw [i1317 hinj, i1316 hinj] at h
  linarith

theorem row504 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2077 + (1 : ℝ) * HLm Γ 5 L2087 + (-1 : ℝ) * HLm Γ 5 L1325 + (-1 : ℝ) * HLm Γ 5 L2084 := by
  have h := HLm_submod hΓ [F0] L2084 [F23]
  rw [show [F0] ++ L2084 ++ [F23] = L2397 from rfl, show [F0] ++ L2084 = L2396 from rfl,
    show L2084 ++ [F23] = L2088 from rfl] at h
  rw [i1319 hinj, i1318 hinj, i1144 hinj] at h
  linarith

theorem row505 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2398 + (1 : ℝ) * HLm Γ 5 L2400 + (-1 : ℝ) * HLm Γ 5 L2402 + (-1 : ℝ) * HLm Γ 5 L2053 := by
  have h := HLm_submod hΓ [F2] L2054 [F9]
  rw [show [F2] ++ L2054 ++ [F9] = L2403 from rfl, show [F2] ++ L2054 = L2399 from rfl,
    show L2054 ++ [F9] = L2401 from rfl] at h
  rw [i1322 hinj, i1320 hinj, i1321 hinj, i1126 hinj] at h
  linarith

theorem row506 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L595 + (1 : ℝ) * HLm Γ 5 L2404 + (-1 : ℝ) * HLm Γ 5 L1348 + (-1 : ℝ) * HLm Γ 5 L972 := by
  have h := HLm_submod hΓ [F0] L973 [F25]
  rw [show [F0] ++ L973 ++ [F25] = L2406 from rfl, show [F0] ++ L973 = L967 from rfl,
    show L973 ++ [F25] = L2405 from rfl] at h
  rw [i1324 hinj, i447 hinj, i1323 hinj, i450 hinj] at h
  linarith

theorem row507 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2407 + (1 : ℝ) * HLm Γ 5 L2409 + (-1 : ℝ) * HLm Γ 5 L2411 + (-1 : ℝ) * HLm Γ 5 L2413 := by
  have h := HLm_submod hΓ [F1] L2414 [F9]
  rw [show [F1] ++ L2414 ++ [F9] = L2412 from rfl, show [F1] ++ L2414 = L2408 from rfl,
    show L2414 ++ [F9] = L2410 from rfl] at h
  rw [i1327 hinj, i1325 hinj, i1326 hinj, i1328 hinj] at h
  linarith

theorem row508 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L845 + (1 : ℝ) * HLm Γ 5 L1035 + (-1 : ℝ) * HLm Γ 5 L1420 + (-1 : ℝ) * HLm Γ 5 L1039 := by
  have h := HLm_submod hΓ [F10] L1040 [F3]
  rw [show [F10] ++ L1040 ++ [F3] = L2416 from rfl, show [F10] ++ L1040 = L2415 from rfl,
    show L1040 ++ [F3] = L1036 from rfl] at h
  rw [i1330 hinj, i1329 hinj, i484 hinj, i486 hinj] at h
  linarith

theorem row509 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2417 + (1 : ℝ) * HLm Γ 5 L2419 + (-1 : ℝ) * HLm Γ 5 L2421 + (-1 : ℝ) * HLm Γ 5 L2423 := by
  have h := HLm_submod hΓ [F2] L2424 [F87]
  rw [show [F2] ++ L2424 ++ [F87] = L2422 from rfl, show [F2] ++ L2424 = L2418 from rfl,
    show L2424 ++ [F87] = L2420 from rfl] at h
  rw [i1333 hinj, i1331 hinj, i1332 hinj, i1334 hinj] at h
  linarith

theorem row510 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1610 + (1 : ℝ) * HLm Γ 5 L454 + (-1 : ℝ) * HLm Γ 5 L1606 + (-1 : ℝ) * HLm Γ 5 L452 := by
  have h := HLm_submod hΓ [F9] L452 [F16]
  rw [show [F9] ++ L452 ++ [F16] = L1607 from rfl, show [F9] ++ L452 = L1611 from rfl,
    show L452 ++ [F16] = L1076 from rfl] at h
  rw [i825 hinj, i827 hinj, i508 hinj] at h
  linarith

theorem row511 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2425 + (1 : ℝ) * HLm Γ 5 L2186 + (-1 : ℝ) * HLm Γ 5 L2428 + (-1 : ℝ) * HLm Γ 5 L2184 := by
  have h := HLm_submod hΓ [F9] L2430 [F23]
  rw [show [F9] ++ L2430 ++ [F23] = L2429 from rfl, show [F9] ++ L2430 = L2426 from rfl,
    show L2430 ++ [F23] = L2427 from rfl] at h
  rw [i1337 hinj, i1335 hinj, i1336 hinj, i1338 hinj] at h
  linarith

theorem row512 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2431 + (1 : ℝ) * HLm Γ 5 L1029 + (-1 : ℝ) * HLm Γ 5 L2433 + (-1 : ℝ) * HLm Γ 5 L362 := by
  have h := HLm_submod hΓ [F1] L363 [F22]
  rw [show [F1] ++ L363 ++ [F22] = L2434 from rfl, show [F1] ++ L363 = L2432 from rfl,
    show L363 ++ [F22] = L1121 from rfl] at h
  rw [i1340 hinj, i1339 hinj, i532 hinj, i144 hinj] at h
  linarith

theorem row513 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2435 + (1 : ℝ) * HLm Γ 5 L2374 + (-1 : ℝ) * HLm Γ 5 L2438 + (-1 : ℝ) * HLm Γ 5 L362 := by
  have h := HLm_submod hΓ [F7] L363 [F12]
  rw [show [F7] ++ L363 ++ [F12] = L2439 from rfl, show [F7] ++ L363 = L2436 from rfl,
    show L363 ++ [F12] = L2437 from rfl] at h
  rw [i1343 hinj, i1341 hinj, i1342 hinj, i144 hinj] at h
  linarith

theorem row514 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2374 + (1 : ℝ) * HLm Γ 5 L2100 + (-1 : ℝ) * HLm Γ 5 L945 + (-1 : ℝ) * HLm Γ 5 L2098 := by
  have h := HLm_submod hΓ [F12] L2099 [F62]
  rw [show [F12] ++ L2099 ++ [F62] = L2442 from rfl, show [F12] ++ L2099 = L2440 from rfl,
    show L2099 ++ [F62] = L2441 from rfl] at h
  rw [i1346 hinj, i1344 hinj, i1345 hinj, i1152 hinj] at h
  linarith

theorem row515 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L511 + (1 : ℝ) * HLm Γ 5 L2444 + (-1 : ℝ) * HLm Γ 5 L2446 + (-1 : ℝ) * HLm Γ 5 L346 := by
  have h := HLm_submod hΓ [F12] L346 [F52]
  rw [show [F12] ++ L346 ++ [F52] = L2447 from rfl, show [F12] ++ L346 = L2443 from rfl,
    show L346 ++ [F52] = L2445 from rfl] at h
  rw [i1349 hinj, i1347 hinj, i1348 hinj] at h
  linarith

theorem row516 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2448 + (1 : ℝ) * HLm Γ 5 L2450 + (-1 : ℝ) * HLm Γ 5 L2452 + (-1 : ℝ) * HLm Γ 5 L1167 := by
  have h := HLm_submod hΓ [F0] L1168 [F3]
  rw [show [F0] ++ L1168 ++ [F3] = L2453 from rfl, show [F0] ++ L1168 = L2449 from rfl,
    show L1168 ++ [F3] = L2451 from rfl] at h
  rw [i1352 hinj, i1350 hinj, i1351 hinj, i559 hinj] at h
  linarith

theorem row517 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2107 + (1 : ℝ) * HLm Γ 5 L2454 + (-1 : ℝ) * HLm Γ 5 L2456 + (-1 : ℝ) * HLm Γ 5 L2105 := by
  have h := HLm_submod hΓ [F12] L2106 [F67]
  rw [show [F12] ++ L2106 ++ [F67] = L2457 from rfl, show [F12] ++ L2106 = L2108 from rfl,
    show L2106 ++ [F67] = L2455 from rfl] at h
  rw [i1354 hinj, i1156 hinj, i1353 hinj, i1155 hinj] at h
  linarith

theorem row518 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2113 + (1 : ℝ) * HLm Γ 5 L2458 + (-1 : ℝ) * HLm Γ 5 L2460 + (-1 : ℝ) * HLm Γ 5 L2111 := by
  have h := HLm_submod hΓ [F62] L2112 [F16]
  rw [show [F62] ++ L2112 ++ [F16] = L2461 from rfl, show [F62] ++ L2112 = L2114 from rfl,
    show L2112 ++ [F16] = L2459 from rfl] at h
  rw [i1356 hinj, i1159 hinj, i1355 hinj, i1158 hinj] at h
  linarith

theorem row519 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2462 + (1 : ℝ) * HLm Γ 5 L2464 + (-1 : ℝ) * HLm Γ 5 L1614 + (-1 : ℝ) * HLm Γ 5 L2120 := by
  have h := HLm_submod hΓ [F1] L2121 [F17]
  rw [show [F1] ++ L2121 ++ [F17] = L2466 from rfl, show [F1] ++ L2121 = L2463 from rfl,
    show L2121 ++ [F17] = L2465 from rfl] at h
  rw [i1359 hinj, i1357 hinj, i1358 hinj, i1162 hinj] at h
  linarith

theorem row520 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1180 + (1 : ℝ) * HLm Γ 5 L2468 + (-1 : ℝ) * HLm Γ 5 L1187 + (-1 : ℝ) * HLm Γ 5 L394 := by
  have h := HLm_submod hΓ [F62] L395 [F3]
  rw [show [F62] ++ L395 ++ [F3] = L2470 from rfl, show [F62] ++ L395 = L2467 from rfl,
    show L395 ++ [F3] = L2469 from rfl] at h
  rw [i1362 hinj, i1360 hinj, i1361 hinj, i158 hinj] at h
  linarith

theorem row521 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2471 + (1 : ℝ) * HLm Γ 5 L2132 + (-1 : ℝ) * HLm Γ 5 L2474 + (-1 : ℝ) * HLm Γ 5 L79 := by
  have h := HLm_submod hΓ [F0] L80 [F2]
  rw [show [F0] ++ L80 ++ [F2] = L2475 from rfl, show [F0] ++ L80 = L2472 from rfl,
    show L80 ++ [F2] = L2473 from rfl] at h
  rw [i1365 hinj, i1363 hinj, i1364 hinj, i18 hinj] at h
  linarith

theorem row522 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2210 + (1 : ℝ) * HLm Γ 5 L2477 + (-1 : ℝ) * HLm Γ 5 L745 + (-1 : ℝ) * HLm Γ 5 L1200 := by
  have h := HLm_submod hΓ [F0] L1201 [F1]
  rw [show [F0] ++ L1201 ++ [F1] = L2479 from rfl, show [F0] ++ L1201 = L2476 from rfl,
    show L1201 ++ [F1] = L2478 from rfl] at h
  rw [i1368 hinj, i1366 hinj, i1367 hinj, i579 hinj] at h
  linarith

theorem row523 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2480 + (1 : ℝ) * HLm Γ 5 L868 + (-1 : ℝ) * HLm Γ 5 L870 + (-1 : ℝ) * HLm Γ 5 L2484 := by
  have h := HLm_submod hΓ [F7] L2485 [F12]
  rw [show [F7] ++ L2485 ++ [F12] = L2483 from rfl, show [F7] ++ L2485 = L2481 from rfl,
    show L2485 ++ [F12] = L2482 from rfl] at h
  rw [i1371 hinj, i1369 hinj, i1370 hinj, i1372 hinj] at h
  linarith

theorem row524 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L97 + (1 : ℝ) * HLm Γ 5 L2155 + (-1 : ℝ) * HLm Γ 5 L599 + (-1 : ℝ) * HLm Γ 5 L2153 := by
  have h := HLm_submod hΓ [F0] L2154 [F16]
  rw [show [F0] ++ L2154 ++ [F16] = L2488 from rfl, show [F0] ++ L2154 = L2486 from rfl,
    show L2154 ++ [F16] = L2487 from rfl] at h
  rw [i1375 hinj, i1373 hinj, i1374 hinj, i1180 hinj] at h
  linarith

theorem row525 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L851 + (1 : ℝ) * HLm Γ 5 L568 + (-1 : ℝ) * HLm Γ 5 L1241 + (-1 : ℝ) * HLm Γ 5 L565 := by
  have h := HLm_submod hΓ [F7] L1248 [F48]
  rw [show [F7] ++ L1248 ++ [F48] = L2490 from rfl, show [F7] ++ L1248 = L1244 from rfl,
    show L1248 ++ [F48] = L2489 from rfl] at h
  rw [i1377 hinj, i603 hinj, i1376 hinj, i606 hinj] at h
  linarith

theorem row526 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2197 + (1 : ℝ) * HLm Γ 5 L2492 + (-1 : ℝ) * HLm Γ 5 L1771 + (-1 : ℝ) * HLm Γ 5 L2495 := by
  have h := HLm_submod hΓ [F2] L2496 [F16]
  rw [show [F2] ++ L2496 ++ [F16] = L2494 from rfl, show [F2] ++ L2496 = L2491 from rfl,
    show L2496 ++ [F16] = L2493 from rfl] at h
  rw [i1380 hinj, i1378 hinj, i1379 hinj, i1381 hinj] at h
  linarith

theorem row527 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L851 + (1 : ℝ) * HLm Γ 5 L2498 + (-1 : ℝ) * HLm Γ 5 L1451 + (-1 : ℝ) * HLm Γ 5 L854 := by
  have h := HLm_submod hΓ [F1] L2501 [F16]
  rw [show [F1] ++ L2501 ++ [F16] = L2500 from rfl, show [F1] ++ L2501 = L2497 from rfl,
    show L2501 ++ [F16] = L2499 from rfl] at h
  rw [i1384 hinj, i1382 hinj, i1383 hinj, i1385 hinj] at h
  linarith

theorem row528 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2502 + (1 : ℝ) * HLm Γ 5 L2474 + (-1 : ℝ) * HLm Γ 5 L2505 + (-1 : ℝ) * HLm Γ 5 L2272 := by
  have h := HLm_submod hΓ [F1] L2273 [F67]
  rw [show [F1] ++ L2273 ++ [F67] = L2506 from rfl, show [F1] ++ L2273 = L2503 from rfl,
    show L2273 ++ [F67] = L2504 from rfl] at h
  rw [i1388 hinj, i1386 hinj, i1387 hinj, i1254 hinj] at h
  linarith

theorem row529 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L851 + (1 : ℝ) * HLm Γ 5 L2508 + (-1 : ℝ) * HLm Γ 5 L842 + (-1 : ℝ) * HLm Γ 5 L2191 := by
  have h := HLm_submod hΓ [F1] L2511 [F45]
  rw [show [F1] ++ L2511 ++ [F45] = L2510 from rfl, show [F1] ++ L2511 = L2507 from rfl,
    show L2511 ++ [F45] = L2509 from rfl] at h
  rw [i1391 hinj, i1389 hinj, i1390 hinj, i1392 hinj] at h
  linarith

theorem row530 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1309 + (1 : ℝ) * HLm Γ 5 L2512 + (-1 : ℝ) * HLm Γ 5 L2514 + (-1 : ℝ) * HLm Γ 5 L1315 := by
  have h := HLm_submod hΓ [F67] L1316 [F36]
  rw [show [F67] ++ L1316 ++ [F36] = L2515 from rfl, show [F67] ++ L1316 = L1310 from rfl,
    show L1316 ++ [F36] = L2513 from rfl] at h
  rw [i1394 hinj, i644 hinj, i1393 hinj, i647 hinj] at h
  linarith

theorem row531 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2516 + (1 : ℝ) * HLm Γ 5 L2518 + (-1 : ℝ) * HLm Γ 5 L2520 + (-1 : ℝ) * HLm Γ 5 L2522 := by
  have h := HLm_submod hΓ [F16] L2523 [F67]
  rw [show [F16] ++ L2523 ++ [F67] = L2521 from rfl, show [F16] ++ L2523 = L2517 from rfl,
    show L2523 ++ [F67] = L2519 from rfl] at h
  rw [i1397 hinj, i1395 hinj, i1396 hinj, i1398 hinj] at h
  linarith

theorem row532 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2241 + (1 : ℝ) * HLm Γ 5 L2525 + (-1 : ℝ) * HLm Γ 5 L1257 + (-1 : ℝ) * HLm Γ 5 L2528 := by
  have h := HLm_submod hΓ [F7] L2529 [F1]
  rw [show [F7] ++ L2529 ++ [F1] = L2527 from rfl, show [F7] ++ L2529 = L2524 from rfl,
    show L2529 ++ [F1] = L2526 from rfl] at h
  rw [i1401 hinj, i1399 hinj, i1400 hinj, i1402 hinj] at h
  linarith

theorem row533 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1819 + (1 : ℝ) * HLm Γ 5 L1778 + (-1 : ℝ) * HLm Γ 5 L1816 + (-1 : ℝ) * HLm Γ 5 L2533 := by
  have h := HLm_submod hΓ [F44] L2534 [F67]
  rw [show [F44] ++ L2534 ++ [F67] = L2532 from rfl, show [F44] ++ L2534 = L2530 from rfl,
    show L2534 ++ [F67] = L2531 from rfl] at h
  rw [i1405 hinj, i1403 hinj, i1404 hinj, i1406 hinj] at h
  linarith

theorem row534 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2535 + (1 : ℝ) * HLm Γ 5 L2214 + (-1 : ℝ) * HLm Γ 5 L2538 + (-1 : ℝ) * HLm Γ 5 L2212 := by
  have h := HLm_submod hΓ [F1] L2540 [F67]
  rw [show [F1] ++ L2540 ++ [F67] = L2539 from rfl, show [F1] ++ L2540 = L2536 from rfl,
    show L2540 ++ [F67] = L2537 from rfl] at h
  rw [i1409 hinj, i1407 hinj, i1408 hinj, i1410 hinj] at h
  linarith

theorem row535 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2541 + (1 : ℝ) * HLm Γ 5 L1348 + (-1 : ℝ) * HLm Γ 5 L1694 + (-1 : ℝ) * HLm Γ 5 L582 := by
  have h := HLm_submod hΓ [F2] L582 [F16]
  rw [show [F2] ++ L582 ++ [F16] = L2543 from rfl, show [F2] ++ L582 = L2542 from rfl,
    show L582 ++ [F16] = L1349 from rfl] at h
  rw [i1412 hinj, i1411 hinj, i667 hinj] at h
  linarith

theorem row536 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2544 + (1 : ℝ) * HLm Γ 5 L599 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L2448 := by
  have h := HLm_submod hΓ [F62] L2449 [F44]
  rw [show [F62] ++ L2449 ++ [F44] = L2547 from rfl, show [F62] ++ L2449 = L2545 from rfl,
    show L2449 ++ [F44] = L2546 from rfl] at h
  rw [i1415 hinj, i1413 hinj, i1414 hinj, i1350 hinj] at h
  linarith

theorem row537 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1630 + (1 : ℝ) * HLm Γ 5 L1093 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L2551 := by
  have h := HLm_submod hΓ [F7] L2552 [F5]
  rw [show [F7] ++ L2552 ++ [F5] = L2550 from rfl, show [F7] ++ L2552 = L2548 from rfl,
    show L2552 ++ [F5] = L2549 from rfl] at h
  rw [i1418 hinj, i1416 hinj, i1417 hinj, i1419 hinj] at h
  linarith

theorem row538 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1323 + (1 : ℝ) * HLm Γ 5 L2227 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L2225 := by
  have h := HLm_submod hΓ [F7] L2556 [F23]
  rw [show [F7] ++ L2556 ++ [F23] = L2555 from rfl, show [F7] ++ L2556 = L2553 from rfl,
    show L2556 ++ [F23] = L2554 from rfl] at h
  rw [i1422 hinj, i1420 hinj, i1421 hinj, i1423 hinj] at h
  linarith

theorem row539 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1995 + (1 : ℝ) * HLm Γ 5 L825 + (-1 : ℝ) * HLm Γ 5 L842 + (-1 : ℝ) * HLm Γ 5 L671 := by
  have h := HLm_submod hΓ [F1] L2560 [F0]
  rw [show [F1] ++ L2560 ++ [F0] = L2559 from rfl, show [F1] ++ L2560 = L2557 from rfl,
    show L2560 ++ [F0] = L2558 from rfl] at h
  rw [i1426 hinj, i1424 hinj, i1425 hinj, i1427 hinj] at h
  linarith

theorem row540 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2561 + (1 : ℝ) * HLm Γ 5 L2563 + (-1 : ℝ) * HLm Γ 5 L2565 + (-1 : ℝ) * HLm Γ 5 L2567 := by
  have h := HLm_submod hΓ [F2] L2568 [F67]
  rw [show [F2] ++ L2568 ++ [F67] = L2566 from rfl, show [F2] ++ L2568 = L2562 from rfl,
    show L2568 ++ [F67] = L2564 from rfl] at h
  rw [i1430 hinj, i1428 hinj, i1429 hinj, i1431 hinj] at h
  linarith

theorem row541 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2232 + (1 : ℝ) * HLm Γ 5 L2569 + (-1 : ℝ) * HLm Γ 5 L1380 + (-1 : ℝ) * HLm Γ 5 L2230 := by
  have h := HLm_submod hΓ [F2] L2231 [F16]
  rw [show [F2] ++ L2231 ++ [F16] = L2571 from rfl, show [F2] ++ L2231 = L2233 from rfl,
    show L2231 ++ [F16] = L2570 from rfl] at h
  rw [i1433 hinj, i1227 hinj, i1432 hinj, i1226 hinj] at h
  linarith

theorem row542 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L851 + (1 : ℝ) * HLm Γ 5 L2572 + (-1 : ℝ) * HLm Γ 5 L842 + (-1 : ℝ) * HLm Γ 5 L1401 := by
  have h := HLm_submod hΓ [F0] L1402 [F45]
  rw [show [F0] ++ L1402 ++ [F45] = L2574 from rfl, show [F0] ++ L1402 = L1397 from rfl,
    show L1402 ++ [F45] = L2573 from rfl] at h
  rw [i1435 hinj, i699 hinj, i1434 hinj, i702 hinj] at h
  linarith

theorem row543 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2575 + (1 : ℝ) * HLm Γ 5 L839 + (-1 : ℝ) * HLm Γ 5 L842 + (-1 : ℝ) * HLm Γ 5 L2579 := by
  have h := HLm_submod hΓ [F1] L2580 [F0]
  rw [show [F1] ++ L2580 ++ [F0] = L2578 from rfl, show [F1] ++ L2580 = L2576 from rfl,
    show L2580 ++ [F0] = L2577 from rfl] at h
  rw [i1438 hinj, i1436 hinj, i1437 hinj, i1439 hinj] at h
  linarith

theorem row544 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L845 + (1 : ℝ) * HLm Γ 5 L1219 + (-1 : ℝ) * HLm Γ 5 L847 + (-1 : ℝ) * HLm Γ 5 L1215 := by
  have h := HLm_submod hΓ [F0] L1215 [F2]
  rw [show [F0] ++ L1215 ++ [F2] = L2582 from rfl, show [F0] ++ L1215 = L845 from rfl,
    show L1215 ++ [F2] = L2581 from rfl] at h
  rw [i1441 hinj, i1440 hinj] at h
  linarith

theorem row545 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L845 + (1 : ℝ) * HLm Γ 5 L2257 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L673 := by
  have h := HLm_submod hΓ [F0] L1426 [F59]
  rw [show [F0] ++ L1426 ++ [F59] = L2584 from rfl, show [F0] ++ L1426 = L1422 from rfl,
    show L1426 ++ [F59] = L2583 from rfl] at h
  rw [i1443 hinj, i713 hinj, i1442 hinj, i716 hinj] at h
  linarith

theorem row546 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2585 + (1 : ℝ) * HLm Γ 5 L2587 + (-1 : ℝ) * HLm Γ 5 L2589 + (-1 : ℝ) * HLm Γ 5 L2591 := by
  have h := HLm_submod hΓ [F0] L2592 [F19]
  rw [show [F0] ++ L2592 ++ [F19] = L2590 from rfl, show [F0] ++ L2592 = L2586 from rfl,
    show L2592 ++ [F19] = L2588 from rfl] at h
  rw [i1446 hinj, i1444 hinj, i1445 hinj, i1447 hinj] at h
  linarith

theorem row547 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2241 + (1 : ℝ) * HLm Γ 5 L2594 + (-1 : ℝ) * HLm Γ 5 L1257 + (-1 : ℝ) * HLm Γ 5 L2597 := by
  have h := HLm_submod hΓ [F0] L2598 [F1]
  rw [show [F0] ++ L2598 ++ [F1] = L2596 from rfl, show [F0] ++ L2598 = L2593 from rfl,
    show L2598 ++ [F1] = L2595 from rfl] at h
  rw [i1450 hinj, i1448 hinj, i1449 hinj, i1451 hinj] at h
  linarith

theorem row548 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L669 + (1 : ℝ) * HLm Γ 5 L2438 + (-1 : ℝ) * HLm Γ 5 L847 + (-1 : ℝ) * HLm Γ 5 L2435 := by
  have h := HLm_submod hΓ [F0] L2436 [F12]
  rw [show [F0] ++ L2436 ++ [F12] = L2600 from rfl, show [F0] ++ L2436 = L2599 from rfl,
    show L2436 ++ [F12] = L2439 from rfl] at h
  rw [i1453 hinj, i1452 hinj, i1343 hinj, i1341 hinj] at h
  linarith

theorem row549 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2601 + (1 : ℝ) * HLm Γ 5 L2250 + (-1 : ℝ) * HLm Γ 5 L1785 + (-1 : ℝ) * HLm Γ 5 L2268 := by
  have h := HLm_submod hΓ [F1] L2605 [F16]
  rw [show [F1] ++ L2605 ++ [F16] = L2604 from rfl, show [F1] ++ L2605 = L2602 from rfl,
    show L2605 ++ [F16] = L2603 from rfl] at h
  rw [i1456 hinj, i1454 hinj, i1455 hinj, i1457 hinj] at h
  linarith

theorem row550 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2402 + (1 : ℝ) * HLm Γ 5 L2607 + (-1 : ℝ) * HLm Γ 5 L2609 + (-1 : ℝ) * HLm Γ 5 L2611 := by
  have h := HLm_submod hΓ [F67] L2612 [F36]
  rw [show [F67] ++ L2612 ++ [F36] = L2610 from rfl, show [F67] ++ L2612 = L2606 from rfl,
    show L2612 ++ [F36] = L2608 from rfl] at h
  rw [i1460 hinj, i1458 hinj, i1459 hinj, i1461 hinj] at h
  linarith

theorem row551 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2382 + (1 : ℝ) * HLm Γ 5 L2614 + (-1 : ℝ) * HLm Γ 5 L2616 + (-1 : ℝ) * HLm Γ 5 L2379 := by
  have h := HLm_submod hΓ [F67] L2380 [F36]
  rw [show [F67] ++ L2380 ++ [F36] = L2617 from rfl, show [F67] ++ L2380 = L2613 from rfl,
    show L2380 ++ [F36] = L2615 from rfl] at h
  rw [i1464 hinj, i1462 hinj, i1463 hinj, i1310 hinj] at h
  linarith

theorem row552 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1298 + (1 : ℝ) * HLm Γ 5 L2619 + (-1 : ℝ) * HLm Γ 5 L2621 + (-1 : ℝ) * HLm Γ 5 L718 := by
  have h := HLm_submod hΓ [F0] L1496 [F26]
  rw [show [F0] ++ L1496 ++ [F26] = L2622 from rfl, show [F0] ++ L1496 = L2618 from rfl,
    show L1496 ++ [F26] = L2620 from rfl] at h
  rw [i1467 hinj, i1465 hinj, i1466 hinj, i757 hinj] at h
  linarith

theorem row553 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1276 + (1 : ℝ) * HLm Γ 5 L2282 + (-1 : ℝ) * HLm Γ 5 L1771 + (-1 : ℝ) * HLm Γ 5 L2280 := by
  have h := HLm_submod hΓ [F0] L2281 [F68]
  rw [show [F0] ++ L2281 ++ [F68] = L2625 from rfl, show [F0] ++ L2281 = L2623 from rfl,
    show L2281 ++ [F68] = L2624 from rfl] at h
  rw [i1470 hinj, i1468 hinj, i1469 hinj, i1258 hinj] at h
  linarith

theorem row554 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L851 + (1 : ℝ) * HLm Γ 5 L2627 + (-1 : ℝ) * HLm Γ 5 L1241 + (-1 : ℝ) * HLm Γ 5 L2290 := by
  have h := HLm_submod hΓ [F0] L2630 [F48]
  rw [show [F0] ++ L2630 ++ [F48] = L2629 from rfl, show [F0] ++ L2630 = L2626 from rfl,
    show L2630 ++ [F48] = L2628 from rfl] at h
  rw [i1473 hinj, i1471 hinj, i1472 hinj, i1474 hinj] at h
  linarith

theorem row555 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L2632 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L2635 := by
  have h := HLm_submod hΓ [F111] L2636 [F67]
  rw [show [F111] ++ L2636 ++ [F67] = L2634 from rfl, show [F111] ++ L2636 = L2631 from rfl,
    show L2636 ++ [F67] = L2633 from rfl] at h
  rw [i1477 hinj, i1475 hinj, i1476 hinj, i1478 hinj] at h
  linarith

theorem row556 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2637 + (1 : ℝ) * HLm Γ 5 L2639 + (-1 : ℝ) * HLm Γ 5 L2641 + (-1 : ℝ) * HLm Γ 5 L2384 := by
  have h := HLm_submod hΓ [F16] L2385 [F20]
  rw [show [F16] ++ L2385 ++ [F20] = L2642 from rfl, show [F16] ++ L2385 = L2638 from rfl,
    show L2385 ++ [F20] = L2640 from rfl] at h
  rw [i1481 hinj, i1479 hinj, i1480 hinj, i1313 hinj] at h
  linarith

theorem row557 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L900 + (1 : ℝ) * HLm Γ 5 L2393 + (-1 : ℝ) * HLm Γ 5 L1731 + (-1 : ℝ) * HLm Γ 5 L2390 := by
  have h := HLm_submod hΓ [F7] L2390 [F16]
  rw [show [F7] ++ L2390 ++ [F16] = L2644 from rfl, show [F7] ++ L2390 = L2643 from rfl,
    show L2390 ++ [F16] = L2394 from rfl] at h
  rw [i1483 hinj, i1482 hinj, i1317 hinj] at h
  linarith

theorem row558 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2393 + (1 : ℝ) * HLm Γ 5 L2646 + (-1 : ℝ) * HLm Γ 5 L2648 + (-1 : ℝ) * HLm Γ 5 L2390 := by
  have h := HLm_submod hΓ [F16] L2390 [F41]
  rw [show [F16] ++ L2390 ++ [F41] = L2649 from rfl, show [F16] ++ L2390 = L2645 from rfl,
    show L2390 ++ [F41] = L2647 from rfl] at h
  rw [i1486 hinj, i1484 hinj, i1485 hinj] at h
  linarith

theorem row559 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L2651 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L2654 := by
  have h := HLm_submod hΓ [F0] L2655 [F67]
  rw [show [F0] ++ L2655 ++ [F67] = L2653 from rfl, show [F0] ++ L2655 = L2650 from rfl,
    show L2655 ++ [F67] = L2652 from rfl] at h
  rw [i1489 hinj, i1487 hinj, i1488 hinj, i1490 hinj] at h
  linarith

theorem row560 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1477 + (1 : ℝ) * HLm Γ 5 L1606 + (-1 : ℝ) * HLm Γ 5 L2658 + (-1 : ℝ) * HLm Γ 5 L776 := by
  have h := HLm_submod hΓ [F51] L2660 [F67]
  rw [show [F51] ++ L2660 ++ [F67] = L2659 from rfl, show [F51] ++ L2660 = L2656 from rfl,
    show L2660 ++ [F67] = L2657 from rfl] at h
  rw [i1493 hinj, i1491 hinj, i1492 hinj, i1494 hinj] at h
  linarith

theorem row561 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1323 + (1 : ℝ) * HLm Γ 5 L2662 + (-1 : ℝ) * HLm Γ 5 L2664 + (-1 : ℝ) * HLm Γ 5 L2666 := by
  have h := HLm_submod hΓ [F0] L2667 [F2]
  rw [show [F0] ++ L2667 ++ [F2] = L2665 from rfl, show [F0] ++ L2667 = L2661 from rfl,
    show L2667 ++ [F2] = L2663 from rfl] at h
  rw [i1497 hinj, i1495 hinj, i1496 hinj, i1498 hinj] at h
  linarith

theorem row562 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2585 + (1 : ℝ) * HLm Γ 5 L2298 + (-1 : ℝ) * HLm Γ 5 L2670 + (-1 : ℝ) * HLm Γ 5 L2672 := by
  have h := HLm_submod hΓ [F0] L2673 [F3]
  rw [show [F0] ++ L2673 ++ [F3] = L2671 from rfl, show [F0] ++ L2673 = L2668 from rfl,
    show L2673 ++ [F3] = L2669 from rfl] at h
  rw [i1501 hinj, i1499 hinj, i1500 hinj, i1502 hinj] at h
  linarith

theorem row563 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L845 + (1 : ℝ) * HLm Γ 5 L2675 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L2332 := by
  have h := HLm_submod hΓ [F0] L2678 [F4]
  rw [show [F0] ++ L2678 ++ [F4] = L2677 from rfl, show [F0] ++ L2678 = L2674 from rfl,
    show L2678 ++ [F4] = L2676 from rfl] at h
  rw [i1505 hinj, i1503 hinj, i1504 hinj, i1506 hinj] at h
  linarith

theorem row564 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L1569 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L1573 := by
  have h := HLm_submod hΓ [F0] L1574 [F67]
  rw [show [F0] ++ L1574 ++ [F67] = L2680 from rfl, show [F0] ++ L1574 = L2679 from rfl,
    show L1574 ++ [F67] = L1570 from rfl] at h
  rw [i1508 hinj, i1507 hinj, i803 hinj, i805 hinj] at h
  linarith

theorem row565 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L831 + (1 : ℝ) * HLm Γ 5 L2681 + (-1 : ℝ) * HLm Γ 5 L2683 + (-1 : ℝ) * HLm Γ 5 L1594 := by
  have h := HLm_submod hΓ [F0] L1595 [F3]
  rw [show [F0] ++ L1595 ++ [F3] = L2684 from rfl, show [F0] ++ L1595 = L1589 from rfl,
    show L1595 ++ [F3] = L2682 from rfl] at h
  rw [i1510 hinj, i814 hinj, i1509 hinj, i817 hinj] at h
  linarith

theorem row566 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2325 + (1 : ℝ) * HLm Γ 5 L2686 + (-1 : ℝ) * HLm Γ 5 L2688 + (-1 : ℝ) * HLm Γ 5 L2323 := by
  have h := HLm_submod hΓ [F67] L2690 [F86]
  rw [show [F67] ++ L2690 ++ [F86] = L2689 from rfl, show [F67] ++ L2690 = L2685 from rfl,
    show L2690 ++ [F86] = L2687 from rfl] at h
  rw [i1513 hinj, i1511 hinj, i1512 hinj, i1514 hinj] at h
  linarith

theorem row567 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L669 + (1 : ℝ) * HLm Γ 5 L2692 + (-1 : ℝ) * HLm Γ 5 L1406 + (-1 : ℝ) * HLm Γ 5 L2695 := by
  have h := HLm_submod hΓ [F0] L2696 [F1]
  rw [show [F0] ++ L2696 ++ [F1] = L2694 from rfl, show [F0] ++ L2696 = L2691 from rfl,
    show L2696 ++ [F1] = L2693 from rfl] at h
  rw [i1517 hinj, i1515 hinj, i1516 hinj, i1518 hinj] at h
  linarith

theorem row568 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2343 + (1 : ℝ) * HLm Γ 5 L2698 + (-1 : ℝ) * HLm Γ 5 L2700 + (-1 : ℝ) * HLm Γ 5 L2341 := by
  have h := HLm_submod hΓ [F0] L2702 [F3]
  rw [show [F0] ++ L2702 ++ [F3] = L2701 from rfl, show [F0] ++ L2702 = L2697 from rfl,
    show L2702 ++ [F3] = L2699 from rfl] at h
  rw [i1521 hinj, i1519 hinj, i1520 hinj, i1522 hinj] at h
  linarith

theorem row569 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2293 + (1 : ℝ) * HLm Γ 5 L945 + (-1 : ℝ) * HLm Γ 5 L2705 + (-1 : ℝ) * HLm Γ 5 L188 := by
  have h := HLm_submod hΓ [F47] L188 [F16]
  rw [show [F47] ++ L188 ++ [F16] = L2706 from rfl, show [F47] ++ L188 = L2703 from rfl,
    show L188 ++ [F16] = L2704 from rfl] at h
  rw [i1525 hinj, i1523 hinj, i1524 hinj] at h
  linarith

theorem row570 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L778 + (1 : ℝ) * HLm Γ 5 L2708 + (-1 : ℝ) * HLm Γ 5 L1601 + (-1 : ℝ) * HLm Γ 5 L2356 := by
  have h := HLm_submod hΓ [F1] L2711 [F67]
  rw [show [F1] ++ L2711 ++ [F67] = L2710 from rfl, show [F1] ++ L2711 = L2707 from rfl,
    show L2711 ++ [F67] = L2709 from rfl] at h
  rw [i1528 hinj, i1526 hinj, i1527 hinj, i1529 hinj] at h
  linarith

theorem row571 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2712 + (1 : ℝ) * HLm Γ 5 L2714 + (-1 : ℝ) * HLm Γ 5 L2716 + (-1 : ℝ) * HLm Γ 5 L2718 := by
  have h := HLm_submod hΓ [F107] L2719 [F67]
  rw [show [F107] ++ L2719 ++ [F67] = L2717 from rfl, show [F107] ++ L2719 = L2713 from rfl,
    show L2719 ++ [F67] = L2715 from rfl] at h
  rw [i1532 hinj, i1530 hinj, i1531 hinj, i1533 hinj] at h
  linarith

theorem row572 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2720 + (1 : ℝ) * HLm Γ 5 L2722 + (-1 : ℝ) * HLm Γ 5 L2724 + (-1 : ℝ) * HLm Γ 5 L2726 := by
  have h := HLm_submod hΓ [F1] L2727 [F42]
  rw [show [F1] ++ L2727 ++ [F42] = L2725 from rfl, show [F1] ++ L2727 = L2721 from rfl,
    show L2727 ++ [F42] = L2723 from rfl] at h
  rw [i1536 hinj, i1534 hinj, i1535 hinj, i1537 hinj] at h
  linarith

theorem row573 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2728 + (1 : ℝ) * HLm Γ 5 L870 + (-1 : ℝ) * HLm Γ 5 L2731 + (-1 : ℝ) * HLm Γ 5 L2733 := by
  have h := HLm_submod hΓ [F1] L2734 [F7]
  rw [show [F1] ++ L2734 ++ [F7] = L2732 from rfl, show [F1] ++ L2734 = L2729 from rfl,
    show L2734 ++ [F7] = L2730 from rfl] at h
  rw [i1540 hinj, i1538 hinj, i1539 hinj, i1541 hinj] at h
  linarith

theorem row574 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2388 + (1 : ℝ) * HLm Γ 5 L2735 + (-1 : ℝ) * HLm Γ 5 L2737 + (-1 : ℝ) * HLm Γ 5 L2386 := by
  have h := HLm_submod hΓ [F47] L2387 [F16]
  rw [show [F47] ++ L2387 ++ [F16] = L2738 from rfl, show [F47] ++ L2387 = L2389 from rfl,
    show L2387 ++ [F16] = L2736 from rfl] at h
  rw [i1543 hinj, i1315 hinj, i1542 hinj, i1314 hinj] at h
  linarith

theorem row575 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2241 + (1 : ℝ) * HLm Γ 5 L2740 + (-1 : ℝ) * HLm Γ 5 L847 + (-1 : ℝ) * HLm Γ 5 L2743 := by
  have h := HLm_submod hΓ [F0] L2744 [F12]
  rw [show [F0] ++ L2744 ++ [F12] = L2742 from rfl, show [F0] ++ L2744 = L2739 from rfl,
    show L2744 ++ [F12] = L2741 from rfl] at h
  rw [i1546 hinj, i1544 hinj, i1545 hinj, i1547 hinj] at h
  linarith

theorem row576 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2745 + (1 : ℝ) * HLm Γ 5 L2747 + (-1 : ℝ) * HLm Γ 5 L2749 + (-1 : ℝ) * HLm Γ 5 L2464 := by
  have h := HLm_submod hΓ [F0] L2751 [F12]
  rw [show [F0] ++ L2751 ++ [F12] = L2750 from rfl, show [F0] ++ L2751 = L2746 from rfl,
    show L2751 ++ [F12] = L2748 from rfl] at h
  rw [i1550 hinj, i1548 hinj, i1549 hinj, i1551 hinj] at h
  linarith

theorem row577 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1093 + (1 : ℝ) * HLm Γ 5 L2708 + (-1 : ℝ) * HLm Γ 5 L1694 + (-1 : ℝ) * HLm Γ 5 L2419 := by
  have h := HLm_submod hΓ [F0] L2420 [F12]
  rw [show [F0] ++ L2420 ++ [F12] = L2754 from rfl, show [F0] ++ L2420 = L2752 from rfl,
    show L2420 ++ [F12] = L2753 from rfl] at h
  rw [i1554 hinj, i1552 hinj, i1553 hinj, i1332 hinj] at h
  linarith

theorem row578 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L2538 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L2535 := by
  have h := HLm_submod hΓ [F7] L2758 [F67]
  rw [show [F7] ++ L2758 ++ [F67] = L2757 from rfl, show [F7] ++ L2758 = L2755 from rfl,
    show L2758 ++ [F67] = L2756 from rfl] at h
  rw [i1557 hinj, i1555 hinj, i1556 hinj, i1558 hinj] at h
  linarith

theorem row579 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L1694 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L2498 := by
  have h := HLm_submod hΓ [F1] L2499 [F67]
  rw [show [F1] ++ L2499 ++ [F67] = L2760 from rfl, show [F1] ++ L2499 = L2500 from rfl,
    show L2499 ++ [F67] = L2759 from rfl] at h
  rw [i1560 hinj, i1384 hinj, i1559 hinj, i1383 hinj] at h
  linarith

theorem row580 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L1758 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L1260 := by
  have h := HLm_submod hΓ [F1] L2764 [F67]
  rw [show [F1] ++ L2764 ++ [F67] = L2763 from rfl, show [F1] ++ L2764 = L2761 from rfl,
    show L2764 ++ [F67] = L2762 from rfl] at h
  rw [i1563 hinj, i1561 hinj, i1562 hinj, i1564 hinj] at h
  linarith

theorem row581 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1241 + (1 : ℝ) * HLm Γ 5 L1694 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L2541 := by
  have h := HLm_submod hΓ [F1] L2768 [F16]
  rw [show [F1] ++ L2768 ++ [F16] = L2767 from rfl, show [F1] ++ L2768 = L2765 from rfl,
    show L2768 ++ [F16] = L2766 from rfl] at h
  rw [i1567 hinj, i1565 hinj, i1566 hinj, i1568 hinj] at h
  linarith

theorem row582 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L842 + (1 : ℝ) * HLm Γ 5 L1949 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L2508 := by
  have h := HLm_submod hΓ [F1] L2509 [F16]
  rw [show [F1] ++ L2509 ++ [F16] = L2770 from rfl, show [F1] ++ L2509 = L2510 from rfl,
    show L2509 ++ [F16] = L2769 from rfl] at h
  rw [i1570 hinj, i1391 hinj, i1569 hinj, i1390 hinj] at h
  linarith

theorem row583 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1406 + (1 : ℝ) * HLm Γ 5 L1264 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L2544 := by
  have h := HLm_submod hΓ [F1] L2774 [F2]
  rw [show [F1] ++ L2774 ++ [F2] = L2773 from rfl, show [F1] ++ L2774 = L2771 from rfl,
    show L2774 ++ [F2] = L2772 from rfl] at h
  rw [i1573 hinj, i1571 hinj, i1572 hinj, i1574 hinj] at h
  linarith

theorem row584 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L2520 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L2516 := by
  have h := HLm_submod hΓ [F1] L2778 [F67]
  rw [show [F1] ++ L2778 ++ [F67] = L2777 from rfl, show [F1] ++ L2778 = L2775 from rfl,
    show L2778 ++ [F67] = L2776 from rfl] at h
  rw [i1577 hinj, i1575 hinj, i1576 hinj, i1578 hinj] at h
  linarith

theorem row585 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L2514 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L2512 := by
  have h := HLm_submod hΓ [F1] L2513 [F67]
  rw [show [F1] ++ L2513 ++ [F67] = L2781 from rfl, show [F1] ++ L2513 = L2779 from rfl,
    show L2513 ++ [F67] = L2780 from rfl] at h
  rw [i1581 hinj, i1579 hinj, i1580 hinj, i1393 hinj] at h
  linarith

theorem row586 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L842 + (1 : ℝ) * HLm Γ 5 L1713 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L2572 := by
  have h := HLm_submod hΓ [F0] L2573 [F16]
  rw [show [F0] ++ L2573 ++ [F16] = L2783 from rfl, show [F0] ++ L2573 = L2574 from rfl,
    show L2573 ++ [F16] = L2782 from rfl] at h
  rw [i1583 hinj, i1435 hinj, i1582 hinj, i1434 hinj] at h
  linarith

theorem row587 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L904 + (1 : ℝ) * HLm Γ 5 L2589 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L2587 := by
  have h := HLm_submod hΓ [F1] L2787 [F0]
  rw [show [F1] ++ L2787 ++ [F0] = L2786 from rfl, show [F1] ++ L2787 = L2784 from rfl,
    show L2787 ++ [F0] = L2785 from rfl] at h
  rw [i1586 hinj, i1584 hinj, i1585 hinj, i1587 hinj] at h
  linarith

theorem row588 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L2609 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L2607 := by
  have h := HLm_submod hΓ [F0] L2608 [F67]
  rw [show [F0] ++ L2608 ++ [F67] = L2790 from rfl, show [F0] ++ L2608 = L2788 from rfl,
    show L2608 ++ [F67] = L2789 from rfl] at h
  rw [i1590 hinj, i1588 hinj, i1589 hinj, i1459 hinj] at h
  linarith

theorem row589 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L2616 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L2614 := by
  have h := HLm_submod hΓ [F0] L2615 [F67]
  rw [show [F0] ++ L2615 ++ [F67] = L2793 from rfl, show [F0] ++ L2615 = L2791 from rfl,
    show L2615 ++ [F67] = L2792 from rfl] at h
  rw [i1593 hinj, i1591 hinj, i1592 hinj, i1463 hinj] at h
  linarith

theorem row590 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L2658 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L1477 := by
  have h := HLm_submod hΓ [F0] L2656 [F67]
  rw [show [F0] ++ L2656 ++ [F67] = L2795 from rfl, show [F0] ++ L2656 = L2794 from rfl,
    show L2656 ++ [F67] = L2659 from rfl] at h
  rw [i1595 hinj, i1594 hinj, i1493 hinj, i1491 hinj] at h
  linarith

theorem row591 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2621 + (1 : ℝ) * HLm Γ 5 L1842 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L2619 := by
  have h := HLm_submod hΓ [F0] L2620 [F7]
  rw [show [F0] ++ L2620 ++ [F7] = L2797 from rfl, show [F0] ++ L2620 = L2622 from rfl,
    show L2620 ++ [F7] = L2796 from rfl] at h
  rw [i1597 hinj, i1467 hinj, i1596 hinj, i1466 hinj] at h
  linarith

theorem row592 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1241 + (1 : ℝ) * HLm Γ 5 L2705 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L2627 := by
  have h := HLm_submod hΓ [F0] L2628 [F16]
  rw [show [F0] ++ L2628 ++ [F16] = L2799 from rfl, show [F0] ++ L2628 = L2629 from rfl,
    show L2628 ++ [F16] = L2798 from rfl] at h
  rw [i1599 hinj, i1473 hinj, i1598 hinj, i1472 hinj] at h
  linarith

theorem row593 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L2737 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L2637 := by
  have h := HLm_submod hΓ [F0] L2803 [F67]
  rw [show [F0] ++ L2803 ++ [F67] = L2802 from rfl, show [F0] ++ L2803 = L2800 from rfl,
    show L2803 ++ [F67] = L2801 from rfl] at h
  rw [i1602 hinj, i1600 hinj, i1601 hinj, i1603 hinj] at h
  linarith

theorem row594 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L2805 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L2808 := by
  have h := HLm_submod hΓ [F0] L2809 [F67]
  rw [show [F0] ++ L2809 ++ [F67] = L2807 from rfl, show [F0] ++ L2809 = L2804 from rfl,
    show L2809 ++ [F67] = L2806 from rfl] at h
  rw [i1606 hinj, i1604 hinj, i1605 hinj, i1607 hinj] at h
  linarith

theorem row595 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L842 + (1 : ℝ) * HLm Γ 5 L2648 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L2646 := by
  have h := HLm_submod hΓ [F0] L2647 [F16]
  rw [show [F0] ++ L2647 ++ [F16] = L2812 from rfl, show [F0] ++ L2647 = L2810 from rfl,
    show L2647 ++ [F16] = L2811 from rfl] at h
  rw [i1610 hinj, i1608 hinj, i1609 hinj, i1485 hinj] at h
  linarith

theorem row596 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2813 + (1 : ℝ) * HLm Γ 5 L1420 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L2817 := by
  have h := HLm_submod hΓ [F1] L2818 [F0]
  rw [show [F1] ++ L2818 ++ [F0] = L2816 from rfl, show [F1] ++ L2818 = L2814 from rfl,
    show L2818 ++ [F0] = L2815 from rfl] at h
  rw [i1613 hinj, i1611 hinj, i1612 hinj, i1614 hinj] at h
  linarith

theorem row597 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L2688 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L2686 := by
  have h := HLm_submod hΓ [F0] L2822 [F67]
  rw [show [F0] ++ L2822 ++ [F67] = L2821 from rfl, show [F0] ++ L2822 = L2819 from rfl,
    show L2822 ++ [F67] = L2820 from rfl] at h
  rw [i1617 hinj, i1615 hinj, i1616 hinj, i1618 hinj] at h
  linarith

theorem row598 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L2716 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L2712 := by
  have h := HLm_submod hΓ [F0] L2826 [F67]
  rw [show [F0] ++ L2826 ++ [F67] = L2825 from rfl, show [F0] ++ L2826 = L2823 from rfl,
    show L2826 ++ [F67] = L2824 from rfl] at h
  rw [i1621 hinj, i1619 hinj, i1620 hinj, i1622 hinj] at h
  linarith

theorem row599 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L2827 + (1 : ℝ) * HLm Γ 5 L2724 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L2722 := by
  have h := HLm_submod hΓ [F0] L2723 [F1]
  rw [show [F0] ++ L2723 ++ [F1] = L2830 from rfl, show [F0] ++ L2723 = L2828 from rfl,
    show L2723 ++ [F1] = L2829 from rfl] at h
  rw [i1625 hinj, i1623 hinj, i1624 hinj, i1535 hinj] at h
  linarith

end EntropyBounds.TwoSet.Certs.R7A5
