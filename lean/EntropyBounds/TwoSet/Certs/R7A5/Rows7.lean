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

theorem row1050 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3779 + (1 : ℝ) * HLm Γ 5 L5100 + (-1 : ℝ) * HLm Γ 5 L5102 + (-1 : ℝ) * HLm Γ 5 L3777 := by
  have h := HLm_submod hΓ [F47] L5104 [F16]
  rw [show [F47] ++ L5104 ++ [F16] = L5103 from rfl, show [F47] ++ L5104 = L5099 from rfl,
    show L5104 ++ [F16] = L5101 from rfl] at h
  rw [i2874 hinj, i2872 hinj, i2873 hinj, i2875 hinj] at h
  linarith

theorem row1051 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5105 + (1 : ℝ) * HLm Γ 5 L5106 + (-1 : ℝ) * HLm Γ 5 L5108 + (-1 : ℝ) * HLm Γ 5 L5110 := by
  have h := HLm_submod hΓ [F7] L5110 [F2]
  rw [show [F7] ++ L5110 ++ [F2] = L5109 from rfl, show [F7] ++ L5110 = L5105 from rfl,
    show L5110 ++ [F2] = L5107 from rfl] at h
  rw [i2877 hinj, i2876 hinj] at h
  linarith

theorem row1052 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5111 + (1 : ℝ) * HLm Γ 5 L5113 + (-1 : ℝ) * HLm Γ 5 L5115 + (-1 : ℝ) * HLm Γ 5 L5117 := by
  have h := HLm_submod hΓ [F0] L5118 [F3]
  rw [show [F0] ++ L5118 ++ [F3] = L5116 from rfl, show [F0] ++ L5118 = L5112 from rfl,
    show L5118 ++ [F3] = L5114 from rfl] at h
  rw [i2880 hinj, i2878 hinj, i2879 hinj, i2881 hinj] at h
  linarith

theorem row1053 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1069 + (1 : ℝ) * HLm Γ 5 L5120 + (-1 : ℝ) * HLm Γ 5 L5122 + (-1 : ℝ) * HLm Γ 5 L961 := by
  have h := HLm_submod hΓ [F0] L5124 [F228]
  rw [show [F0] ++ L5124 ++ [F228] = L5123 from rfl, show [F0] ++ L5124 = L5119 from rfl,
    show L5124 ++ [F228] = L5121 from rfl] at h
  rw [i2884 hinj, i2882 hinj, i2883 hinj, i2885 hinj] at h
  linarith

theorem row1054 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5125 + (1 : ℝ) * HLm Γ 5 L3820 + (-1 : ℝ) * HLm Γ 5 L5128 + (-1 : ℝ) * HLm Γ 5 L5130 := by
  have h := HLm_submod hΓ [F0] L5131 [F6]
  rw [show [F0] ++ L5131 ++ [F6] = L5129 from rfl, show [F0] ++ L5131 = L5126 from rfl,
    show L5131 ++ [F6] = L5127 from rfl] at h
  rw [i2888 hinj, i2886 hinj, i2887 hinj, i2889 hinj] at h
  linarith

theorem row1055 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5132 + (1 : ℝ) * HLm Γ 5 L5134 + (-1 : ℝ) * HLm Γ 5 L5136 + (-1 : ℝ) * HLm Γ 5 L3816 := by
  have h := HLm_submod hΓ [F210] L5138 [F17]
  rw [show [F210] ++ L5138 ++ [F17] = L5137 from rfl, show [F210] ++ L5138 = L5133 from rfl,
    show L5138 ++ [F17] = L5135 from rfl] at h
  rw [i2892 hinj, i2890 hinj, i2891 hinj, i2893 hinj] at h
  linarith

theorem row1056 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5139 + (1 : ℝ) * HLm Γ 5 L3820 + (-1 : ℝ) * HLm Γ 5 L5128 + (-1 : ℝ) * HLm Γ 5 L3818 := by
  have h := HLm_submod hΓ [F0] L5143 [F82]
  rw [show [F0] ++ L5143 ++ [F82] = L5142 from rfl, show [F0] ++ L5143 = L5140 from rfl,
    show L5143 ++ [F82] = L5141 from rfl] at h
  rw [i2896 hinj, i2894 hinj, i2895 hinj, i2897 hinj] at h
  linarith

theorem row1057 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5144 + (1 : ℝ) * HLm Γ 5 L3820 + (-1 : ℝ) * HLm Γ 5 L5146 + (-1 : ℝ) * HLm Γ 5 L3818 := by
  have h := HLm_submod hΓ [F7] L5143 [F82]
  rw [show [F7] ++ L5143 ++ [F82] = L5147 from rfl, show [F7] ++ L5143 = L5145 from rfl,
    show L5143 ++ [F82] = L5141 from rfl] at h
  rw [i2899 hinj, i2898 hinj, i2895 hinj, i2897 hinj] at h
  linarith

theorem row1058 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5148 + (1 : ℝ) * HLm Γ 5 L4793 + (-1 : ℝ) * HLm Γ 5 L5151 + (-1 : ℝ) * HLm Γ 5 L3802 := by
  have h := HLm_submod hΓ [F1] L3803 [F9]
  rw [show [F1] ++ L3803 ++ [F9] = L5152 from rfl, show [F1] ++ L3803 = L5149 from rfl,
    show L3803 ++ [F9] = L5150 from rfl] at h
  rw [i2902 hinj, i2900 hinj, i2901 hinj, i2126 hinj] at h
  linarith

theorem row1059 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5153 + (1 : ℝ) * HLm Γ 5 L3545 + (-1 : ℝ) * HLm Γ 5 L5156 + (-1 : ℝ) * HLm Γ 5 L5158 := by
  have h := HLm_submod hΓ [F2] L5159 [F9]
  rw [show [F2] ++ L5159 ++ [F9] = L5157 from rfl, show [F2] ++ L5159 = L5154 from rfl,
    show L5159 ++ [F9] = L5155 from rfl] at h
  rw [i2905 hinj, i2903 hinj, i2904 hinj, i2906 hinj] at h
  linarith

theorem row1060 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5160 + (1 : ℝ) * HLm Γ 5 L5162 + (-1 : ℝ) * HLm Γ 5 L5164 + (-1 : ℝ) * HLm Γ 5 L1013 := by
  have h := HLm_submod hΓ [F0] L1715 [F228]
  rw [show [F0] ++ L1715 ++ [F228] = L5165 from rfl, show [F0] ++ L1715 = L5161 from rfl,
    show L1715 ++ [F228] = L5163 from rfl] at h
  rw [i2909 hinj, i2907 hinj, i2908 hinj, i891 hinj] at h
  linarith

theorem row1061 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5166 + (1 : ℝ) * HLm Γ 5 L5168 + (-1 : ℝ) * HLm Γ 5 L5170 + (-1 : ℝ) * HLm Γ 5 L1053 := by
  have h := HLm_submod hΓ [F9] L5172 [F210]
  rw [show [F9] ++ L5172 ++ [F210] = L5171 from rfl, show [F9] ++ L5172 = L5167 from rfl,
    show L5172 ++ [F210] = L5169 from rfl] at h
  rw [i2912 hinj, i2910 hinj, i2911 hinj, i2913 hinj] at h
  linarith

theorem row1062 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5173 + (1 : ℝ) * HLm Γ 5 L3911 + (-1 : ℝ) * HLm Γ 5 L5175 + (-1 : ℝ) * HLm Γ 5 L3908 := by
  have h := HLm_submod hΓ [F1] L3909 [F228]
  rw [show [F1] ++ L3909 ++ [F228] = L5176 from rfl, show [F1] ++ L3909 = L5174 from rfl,
    show L3909 ++ [F228] = L3912 from rfl] at h
  rw [i2915 hinj, i2914 hinj, i2184 hinj, i2182 hinj] at h
  linarith

theorem row1063 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5177 + (1 : ℝ) * HLm Γ 5 L5179 + (-1 : ℝ) * HLm Γ 5 L5181 + (-1 : ℝ) * HLm Γ 5 L5183 := by
  have h := HLm_submod hΓ [F46] L5184 [F210]
  rw [show [F46] ++ L5184 ++ [F210] = L5182 from rfl, show [F46] ++ L5184 = L5178 from rfl,
    show L5184 ++ [F210] = L5180 from rfl] at h
  rw [i2918 hinj, i2916 hinj, i2917 hinj, i2919 hinj] at h
  linarith

theorem row1064 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1716 + (1 : ℝ) * HLm Γ 5 L5186 + (-1 : ℝ) * HLm Γ 5 L5188 + (-1 : ℝ) * HLm Γ 5 L1091 := by
  have h := HLm_submod hΓ [F1] L5190 [F214]
  rw [show [F1] ++ L5190 ++ [F214] = L5189 from rfl, show [F1] ++ L5190 = L5185 from rfl,
    show L5190 ++ [F214] = L5187 from rfl] at h
  rw [i2922 hinj, i2920 hinj, i2921 hinj, i2923 hinj] at h
  linarith

theorem row1065 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3855 + (1 : ℝ) * HLm Γ 5 L3848 + (-1 : ℝ) * HLm Γ 5 L5192 + (-1 : ℝ) * HLm Γ 5 L3853 := by
  have h := HLm_submod hΓ [F0] L3854 [F23]
  rw [show [F0] ++ L3854 ++ [F23] = L5193 from rfl, show [F0] ++ L3854 = L3856 from rfl,
    show L3854 ++ [F23] = L5191 from rfl] at h
  rw [i2925 hinj, i2154 hinj, i2924 hinj, i2153 hinj] at h
  linarith

theorem row1066 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5194 + (1 : ℝ) * HLm Γ 5 L3871 + (-1 : ℝ) * HLm Γ 5 L5197 + (-1 : ℝ) * HLm Γ 5 L3869 := by
  have h := HLm_submod hΓ [F2] L3870 [F228]
  rw [show [F2] ++ L3870 ++ [F228] = L5198 from rfl, show [F2] ++ L3870 = L5195 from rfl,
    show L3870 ++ [F228] = L5196 from rfl] at h
  rw [i2928 hinj, i2926 hinj, i2927 hinj, i2161 hinj] at h
  linarith

theorem row1067 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3739 + (1 : ℝ) * HLm Γ 5 L4144 + (-1 : ℝ) * HLm Γ 5 L5076 + (-1 : ℝ) * HLm Γ 5 L3861 := by
  have h := HLm_submod hΓ [F44] L3862 [F67]
  rw [show [F44] ++ L3862 ++ [F67] = L5201 from rfl, show [F44] ++ L3862 = L5199 from rfl,
    show L3862 ++ [F67] = L5200 from rfl] at h
  rw [i2931 hinj, i2929 hinj, i2930 hinj, i2157 hinj] at h
  linarith

theorem row1068 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3431 + (1 : ℝ) * HLm Γ 5 L5203 + (-1 : ℝ) * HLm Γ 5 L5205 + (-1 : ℝ) * HLm Γ 5 L5207 := by
  have h := HLm_submod hΓ [F2] L5208 [F85]
  rw [show [F2] ++ L5208 ++ [F85] = L5206 from rfl, show [F2] ++ L5208 = L5202 from rfl,
    show L5208 ++ [F85] = L5204 from rfl] at h
  rw [i2934 hinj, i2932 hinj, i2933 hinj, i2935 hinj] at h
  linarith

theorem row1069 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3992 + (1 : ℝ) * HLm Γ 5 L5210 + (-1 : ℝ) * HLm Γ 5 L5212 + (-1 : ℝ) * HLm Γ 5 L5214 := by
  have h := HLm_submod hΓ [F2] L5215 [F22]
  rw [show [F2] ++ L5215 ++ [F22] = L5213 from rfl, show [F2] ++ L5215 = L5209 from rfl,
    show L5215 ++ [F22] = L5211 from rfl] at h
  rw [i2938 hinj, i2936 hinj, i2937 hinj, i2939 hinj] at h
  linarith

theorem row1070 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5216 + (1 : ℝ) * HLm Γ 5 L5218 + (-1 : ℝ) * HLm Γ 5 L5220 + (-1 : ℝ) * HLm Γ 5 L5222 := by
  have h := HLm_submod hΓ [F10] L5223 [F55]
  rw [show [F10] ++ L5223 ++ [F55] = L5221 from rfl, show [F10] ++ L5223 = L5217 from rfl,
    show L5223 ++ [F55] = L5219 from rfl] at h
  rw [i2942 hinj, i2940 hinj, i2941 hinj, i2943 hinj] at h
  linarith

theorem row1071 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5224 + (1 : ℝ) * HLm Γ 5 L4119 + (-1 : ℝ) * HLm Γ 5 L5226 + (-1 : ℝ) * HLm Γ 5 L3118 := by
  have h := HLm_submod hΓ [F0] L4116 [F210]
  rw [show [F0] ++ L4116 ++ [F210] = L5227 from rfl, show [F0] ++ L4116 = L5225 from rfl,
    show L4116 ++ [F210] = L4120 from rfl] at h
  rw [i2945 hinj, i2944 hinj, i2298 hinj, i2296 hinj] at h
  linarith

theorem row1072 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5228 + (1 : ℝ) * HLm Γ 5 L5230 + (-1 : ℝ) * HLm Γ 5 L5232 + (-1 : ℝ) * HLm Γ 5 L5234 := by
  have h := HLm_submod hΓ [F1] L5235 [F9]
  rw [show [F1] ++ L5235 ++ [F9] = L5233 from rfl, show [F1] ++ L5235 = L5229 from rfl,
    show L5235 ++ [F9] = L5231 from rfl] at h
  rw [i2948 hinj, i2946 hinj, i2947 hinj, i2949 hinj] at h
  linarith

theorem row1073 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5236 + (1 : ℝ) * HLm Γ 5 L3906 + (-1 : ℝ) * HLm Γ 5 L5239 + (-1 : ℝ) * HLm Γ 5 L3904 := by
  have h := HLm_submod hΓ [F0] L5241 [F90]
  rw [show [F0] ++ L5241 ++ [F90] = L5240 from rfl, show [F0] ++ L5241 = L5237 from rfl,
    show L5241 ++ [F90] = L5238 from rfl] at h
  rw [i2952 hinj, i2950 hinj, i2951 hinj, i2953 hinj] at h
  linarith

theorem row1074 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3886 + (1 : ℝ) * HLm Γ 5 L3920 + (-1 : ℝ) * HLm Γ 5 L5244 + (-1 : ℝ) * HLm Γ 5 L3918 := by
  have h := HLm_submod hΓ [F0] L5246 [F3]
  rw [show [F0] ++ L5246 ++ [F3] = L5245 from rfl, show [F0] ++ L5246 = L5242 from rfl,
    show L5246 ++ [F3] = L5243 from rfl] at h
  rw [i2956 hinj, i2954 hinj, i2955 hinj, i2957 hinj] at h
  linarith

theorem row1075 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3883 + (1 : ℝ) * HLm Γ 5 L3935 + (-1 : ℝ) * HLm Γ 5 L5249 + (-1 : ℝ) * HLm Γ 5 L3933 := by
  have h := HLm_submod hΓ [F0] L5251 [F2]
  rw [show [F0] ++ L5251 ++ [F2] = L5250 from rfl, show [F0] ++ L5251 = L5247 from rfl,
    show L5251 ++ [F2] = L5248 from rfl] at h
  rw [i2960 hinj, i2958 hinj, i2959 hinj, i2961 hinj] at h
  linarith

theorem row1076 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3901 + (1 : ℝ) * HLm Γ 5 L3929 + (-1 : ℝ) * HLm Γ 5 L5253 + (-1 : ℝ) * HLm Γ 5 L3899 := by
  have h := HLm_submod hΓ [F1] L3900 [F85]
  rw [show [F1] ++ L3900 ++ [F85] = L5254 from rfl, show [F1] ++ L3900 = L3902 from rfl,
    show L3900 ++ [F85] = L5252 from rfl] at h
  rw [i2963 hinj, i2179 hinj, i2962 hinj, i2178 hinj] at h
  linarith

theorem row1077 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5255 + (1 : ℝ) * HLm Γ 5 L5257 + (-1 : ℝ) * HLm Γ 5 L5259 + (-1 : ℝ) * HLm Γ 5 L3927 := by
  have h := HLm_submod hΓ [F46] L5261 [F210]
  rw [show [F46] ++ L5261 ++ [F210] = L5260 from rfl, show [F46] ++ L5261 = L5256 from rfl,
    show L5261 ++ [F210] = L5258 from rfl] at h
  rw [i2966 hinj, i2964 hinj, i2965 hinj, i2967 hinj] at h
  linarith

theorem row1078 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5262 + (1 : ℝ) * HLm Γ 5 L5264 + (-1 : ℝ) * HLm Γ 5 L5266 + (-1 : ℝ) * HLm Γ 5 L3941 := by
  have h := HLm_submod hΓ [F2] L3942 [F9]
  rw [show [F2] ++ L3942 ++ [F9] = L5267 from rfl, show [F2] ++ L3942 = L5263 from rfl,
    show L3942 ++ [F9] = L5265 from rfl] at h
  rw [i2970 hinj, i2968 hinj, i2969 hinj, i2200 hinj] at h
  linarith

theorem row1079 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5268 + (1 : ℝ) * HLm Γ 5 L3956 + (-1 : ℝ) * HLm Γ 5 L5271 + (-1 : ℝ) * HLm Γ 5 L3954 := by
  have h := HLm_submod hΓ [F3] L3955 [F210]
  rw [show [F3] ++ L3955 ++ [F210] = L5272 from rfl, show [F3] ++ L3955 = L5269 from rfl,
    show L3955 ++ [F210] = L5270 from rfl] at h
  rw [i2973 hinj, i2971 hinj, i2972 hinj, i2207 hinj] at h
  linarith

theorem row1080 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5273 + (1 : ℝ) * HLm Γ 5 L5275 + (-1 : ℝ) * HLm Γ 5 L5277 + (-1 : ℝ) * HLm Γ 5 L5279 := by
  have h := HLm_submod hΓ [F0] L5280 [F3]
  rw [show [F0] ++ L5280 ++ [F3] = L5278 from rfl, show [F0] ++ L5280 = L5274 from rfl,
    show L5280 ++ [F3] = L5276 from rfl] at h
  rw [i2976 hinj, i2974 hinj, i2975 hinj, i2977 hinj] at h
  linarith

theorem row1081 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5281 + (1 : ℝ) * HLm Γ 5 L3962 + (-1 : ℝ) * HLm Γ 5 L5284 + (-1 : ℝ) * HLm Γ 5 L3960 := by
  have h := HLm_submod hΓ [F62] L3961 [F210]
  rw [show [F62] ++ L3961 ++ [F210] = L5285 from rfl, show [F62] ++ L3961 = L5282 from rfl,
    show L3961 ++ [F210] = L5283 from rfl] at h
  rw [i2980 hinj, i2978 hinj, i2979 hinj, i2210 hinj] at h
  linarith

theorem row1082 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L3980 + (1 : ℝ) * HLm Γ 5 L5287 + (-1 : ℝ) * HLm Γ 5 L5289 + (-1 : ℝ) * HLm Γ 5 L3978 := by
  have h := HLm_submod hΓ [F2] L5291 [F9]
  rw [show [F2] ++ L5291 ++ [F9] = L5290 from rfl, show [F2] ++ L5291 = L5286 from rfl,
    show L5291 ++ [F9] = L5288 from rfl] at h
  rw [i2983 hinj, i2981 hinj, i2982 hinj, i2984 hinj] at h
  linarith

theorem row1083 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5292 + (1 : ℝ) * HLm Γ 5 L5294 + (-1 : ℝ) * HLm Γ 5 L5296 + (-1 : ℝ) * HLm Γ 5 L3970 := by
  have h := HLm_submod hΓ [F210] L3971 [F36]
  rw [show [F210] ++ L3971 ++ [F36] = L5297 from rfl, show [F210] ++ L3971 = L5293 from rfl,
    show L3971 ++ [F36] = L5295 from rfl] at h
  rw [i2987 hinj, i2985 hinj, i2986 hinj, i2216 hinj] at h
  linarith

theorem row1084 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5298 + (1 : ℝ) * HLm Γ 5 L5300 + (-1 : ℝ) * HLm Γ 5 L5302 + (-1 : ℝ) * HLm Γ 5 L5304 := by
  have h := HLm_submod hΓ [F44] L5305 [F210]
  rw [show [F44] ++ L5305 ++ [F210] = L5303 from rfl, show [F44] ++ L5305 = L5299 from rfl,
    show L5305 ++ [F210] = L5301 from rfl] at h
  rw [i2990 hinj, i2988 hinj, i2989 hinj, i2991 hinj] at h
  linarith

theorem row1085 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5306 + (1 : ℝ) * HLm Γ 5 L4005 + (-1 : ℝ) * HLm Γ 5 L5309 + (-1 : ℝ) * HLm Γ 5 L4003 := by
  have h := HLm_submod hΓ [F1] L5311 [F9]
  rw [show [F1] ++ L5311 ++ [F9] = L5310 from rfl, show [F1] ++ L5311 = L5307 from rfl,
    show L5311 ++ [F9] = L5308 from rfl] at h
  rw [i2994 hinj, i2992 hinj, i2993 hinj, i2995 hinj] at h
  linarith

theorem row1086 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5312 + (1 : ℝ) * HLm Γ 5 L5314 + (-1 : ℝ) * HLm Γ 5 L5316 + (-1 : ℝ) * HLm Γ 5 L5318 := by
  have h := HLm_submod hΓ [F1] L5319 [F27]
  rw [show [F1] ++ L5319 ++ [F27] = L5317 from rfl, show [F1] ++ L5319 = L5313 from rfl,
    show L5319 ++ [F27] = L5315 from rfl] at h
  rw [i2998 hinj, i2996 hinj, i2997 hinj, i2999 hinj] at h
  linarith

theorem row1087 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1083 + (1 : ℝ) * HLm Γ 5 L3999 + (-1 : ℝ) * HLm Γ 5 L5322 + (-1 : ℝ) * HLm Γ 5 L3997 := by
  have h := HLm_submod hΓ [F1] L3998 [F214]
  rw [show [F1] ++ L3998 ++ [F214] = L5323 from rfl, show [F1] ++ L3998 = L5320 from rfl,
    show L3998 ++ [F214] = L5321 from rfl] at h
  rw [i3002 hinj, i3000 hinj, i3001 hinj, i2231 hinj] at h
  linarith

theorem row1088 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5324 + (1 : ℝ) * HLm Γ 5 L5022 + (-1 : ℝ) * HLm Γ 5 L5327 + (-1 : ℝ) * HLm Γ 5 L4026 := by
  have h := HLm_submod hΓ [F0] L4027 [F3]
  rw [show [F0] ++ L4027 ++ [F3] = L5328 from rfl, show [F0] ++ L4027 = L5325 from rfl,
    show L4027 ++ [F3] = L5326 from rfl] at h
  rw [i3005 hinj, i3003 hinj, i3004 hinj, i2247 hinj] at h
  linarith

theorem row1089 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5329 + (1 : ℝ) * HLm Γ 5 L5331 + (-1 : ℝ) * HLm Γ 5 L5333 + (-1 : ℝ) * HLm Γ 5 L4034 := by
  have h := HLm_submod hΓ [F0] L4035 [F2]
  rw [show [F0] ++ L4035 ++ [F2] = L5334 from rfl, show [F0] ++ L4035 = L5330 from rfl,
    show L4035 ++ [F2] = L5332 from rfl] at h
  rw [i3008 hinj, i3006 hinj, i3007 hinj, i2251 hinj] at h
  linarith

theorem row1090 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4074 + (1 : ℝ) * HLm Γ 5 L5335 + (-1 : ℝ) * HLm Γ 5 L5337 + (-1 : ℝ) * HLm Γ 5 L4072 := by
  have h := HLm_submod hΓ [F9] L4073 [F16]
  rw [show [F9] ++ L4073 ++ [F16] = L5338 from rfl, show [F9] ++ L4073 = L4075 from rfl,
    show L4073 ++ [F16] = L5336 from rfl] at h
  rw [i3010 hinj, i2273 hinj, i3009 hinj, i2272 hinj] at h
  linarith

theorem row1091 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5339 + (1 : ℝ) * HLm Γ 5 L5341 + (-1 : ℝ) * HLm Γ 5 L5343 + (-1 : ℝ) * HLm Γ 5 L4085 := by
  have h := HLm_submod hΓ [F7] L4086 [F217]
  rw [show [F7] ++ L4086 ++ [F217] = L5344 from rfl, show [F7] ++ L4086 = L5340 from rfl,
    show L4086 ++ [F217] = L5342 from rfl] at h
  rw [i3013 hinj, i3011 hinj, i3012 hinj, i2279 hinj] at h
  linarith

theorem row1092 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4081 + (1 : ℝ) * HLm Γ 5 L5345 + (-1 : ℝ) * HLm Γ 5 L5347 + (-1 : ℝ) * HLm Γ 5 L4079 := by
  have h := HLm_submod hΓ [F2] L4080 [F67]
  rw [show [F2] ++ L4080 ++ [F67] = L5348 from rfl, show [F2] ++ L4080 = L4082 from rfl,
    show L4080 ++ [F67] = L5346 from rfl] at h
  rw [i3015 hinj, i2277 hinj, i3014 hinj, i2276 hinj] at h
  linarith

theorem row1093 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5349 + (1 : ℝ) * HLm Γ 5 L4092 + (-1 : ℝ) * HLm Γ 5 L5352 + (-1 : ℝ) * HLm Γ 5 L4090 := by
  have h := HLm_submod hΓ [F2] L4091 [F85]
  rw [show [F2] ++ L4091 ++ [F85] = L5353 from rfl, show [F2] ++ L4091 = L5350 from rfl,
    show L4091 ++ [F85] = L5351 from rfl] at h
  rw [i3018 hinj, i3016 hinj, i3017 hinj, i2282 hinj] at h
  linarith

theorem row1094 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4634 + (1 : ℝ) * HLm Γ 5 L5355 + (-1 : ℝ) * HLm Γ 5 L5357 + (-1 : ℝ) * HLm Γ 5 L4106 := by
  have h := HLm_submod hΓ [F4] L5359 [F68]
  rw [show [F4] ++ L5359 ++ [F68] = L5358 from rfl, show [F4] ++ L5359 = L5354 from rfl,
    show L5359 ++ [F68] = L5356 from rfl] at h
  rw [i3021 hinj, i3019 hinj, i3020 hinj, i3022 hinj] at h
  linarith

theorem row1095 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5360 + (1 : ℝ) * HLm Γ 5 L4114 + (-1 : ℝ) * HLm Γ 5 L5363 + (-1 : ℝ) * HLm Γ 5 L4112 := by
  have h := HLm_submod hΓ [F46] L4113 [F210]
  rw [show [F46] ++ L4113 ++ [F210] = L5364 from rfl, show [F46] ++ L4113 = L5361 from rfl,
    show L4113 ++ [F210] = L5362 from rfl] at h
  rw [i3025 hinj, i3023 hinj, i3024 hinj, i2294 hinj] at h
  linarith

theorem row1096 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5365 + (1 : ℝ) * HLm Γ 5 L5228 + (-1 : ℝ) * HLm Γ 5 L5368 + (-1 : ℝ) * HLm Γ 5 L4181 := by
  have h := HLm_submod hΓ [F0] L5370 [F1]
  rw [show [F0] ++ L5370 ++ [F1] = L5369 from rfl, show [F0] ++ L5370 = L5366 from rfl,
    show L5370 ++ [F1] = L5367 from rfl] at h
  rw [i3028 hinj, i3026 hinj, i3027 hinj, i3029 hinj] at h
  linarith

theorem row1097 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5371 + (1 : ℝ) * HLm Γ 5 L5373 + (-1 : ℝ) * HLm Γ 5 L5375 + (-1 : ℝ) * HLm Γ 5 L5377 := by
  have h := HLm_submod hΓ [F210] L5378 [F6]
  rw [show [F210] ++ L5378 ++ [F6] = L5376 from rfl, show [F210] ++ L5378 = L5372 from rfl,
    show L5378 ++ [F6] = L5374 from rfl] at h
  rw [i3032 hinj, i3030 hinj, i3031 hinj, i3033 hinj] at h
  linarith

theorem row1098 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4366 + (1 : ℝ) * HLm Γ 5 L4566 + (-1 : ℝ) * HLm Γ 5 L5381 + (-1 : ℝ) * HLm Γ 5 L4364 := by
  have h := HLm_submod hΓ [F2] L5383 [F7]
  rw [show [F2] ++ L5383 ++ [F7] = L5382 from rfl, show [F2] ++ L5383 = L5379 from rfl,
    show L5383 ++ [F7] = L5380 from rfl] at h
  rw [i3036 hinj, i3034 hinj, i3035 hinj, i3037 hinj] at h
  linarith

theorem row1099 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5384 + (1 : ℝ) * HLm Γ 5 L5386 + (-1 : ℝ) * HLm Γ 5 L5381 + (-1 : ℝ) * HLm Γ 5 L5389 := by
  have h := HLm_submod hΓ [F1] L5390 [F45]
  rw [show [F1] ++ L5390 ++ [F45] = L5388 from rfl, show [F1] ++ L5390 = L5385 from rfl,
    show L5390 ++ [F45] = L5387 from rfl] at h
  rw [i3040 hinj, i3038 hinj, i3039 hinj, i3041 hinj] at h
  linarith

theorem row1100 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5391 + (1 : ℝ) * HLm Γ 5 L4194 + (-1 : ℝ) * HLm Γ 5 L5394 + (-1 : ℝ) * HLm Γ 5 L4192 := by
  have h := HLm_submod hΓ [F22] L4193 [F210]
  rw [show [F22] ++ L4193 ++ [F210] = L5395 from rfl, show [F22] ++ L4193 = L5392 from rfl,
    show L4193 ++ [F210] = L5393 from rfl] at h
  rw [i3044 hinj, i3042 hinj, i3043 hinj, i2341 hinj] at h
  linarith

theorem row1101 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4199 + (1 : ℝ) * HLm Γ 5 L5397 + (-1 : ℝ) * HLm Γ 5 L5399 + (-1 : ℝ) * HLm Γ 5 L3629 := by
  have h := HLm_submod hΓ [F67] L5401 [F236]
  rw [show [F67] ++ L5401 ++ [F236] = L5400 from rfl, show [F67] ++ L5401 = L5396 from rfl,
    show L5401 ++ [F236] = L5398 from rfl] at h
  rw [i3047 hinj, i3045 hinj, i3046 hinj, i3048 hinj] at h
  linarith

theorem row1102 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L5403 + (-1 : ℝ) * HLm Γ 5 L4558 + (-1 : ℝ) * HLm Γ 5 L5406 := by
  have h := HLm_submod hΓ [F1] L5407 [F219]
  rw [show [F1] ++ L5407 ++ [F219] = L5405 from rfl, show [F1] ++ L5407 = L5402 from rfl,
    show L5407 ++ [F219] = L5404 from rfl] at h
  rw [i3051 hinj, i3049 hinj, i3050 hinj, i3052 hinj] at h
  linarith

theorem row1103 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5408 + (1 : ℝ) * HLm Γ 5 L5410 + (-1 : ℝ) * HLm Γ 5 L5412 + (-1 : ℝ) * HLm Γ 5 L4208 := by
  have h := HLm_submod hΓ [F107] L4209 [F210]
  rw [show [F107] ++ L4209 ++ [F210] = L5413 from rfl, show [F107] ++ L4209 = L5409 from rfl,
    show L4209 ++ [F210] = L5411 from rfl] at h
  rw [i3055 hinj, i3053 hinj, i3054 hinj, i2352 hinj] at h
  linarith

theorem row1104 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1758 + (1 : ℝ) * HLm Γ 5 L5239 + (-1 : ℝ) * HLm Γ 5 L5416 + (-1 : ℝ) * HLm Γ 5 L5418 := by
  have h := HLm_submod hΓ [F2] L5419 [F210]
  rw [show [F2] ++ L5419 ++ [F210] = L5417 from rfl, show [F2] ++ L5419 = L5414 from rfl,
    show L5419 ++ [F210] = L5415 from rfl] at h
  rw [i3058 hinj, i3056 hinj, i3057 hinj, i3059 hinj] at h
  linarith

theorem row1105 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5420 + (1 : ℝ) * HLm Γ 5 L4230 + (-1 : ℝ) * HLm Γ 5 L5423 + (-1 : ℝ) * HLm Γ 5 L4228 := by
  have h := HLm_submod hΓ [F108] L4229 [F210]
  rw [show [F108] ++ L4229 ++ [F210] = L5424 from rfl, show [F108] ++ L4229 = L5421 from rfl,
    show L4229 ++ [F210] = L5422 from rfl] at h
  rw [i3062 hinj, i3060 hinj, i3061 hinj, i2363 hinj] at h
  linarith

theorem row1106 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L5426 + (-1 : ℝ) * HLm Γ 5 L4558 + (-1 : ℝ) * HLm Γ 5 L5429 := by
  have h := HLm_submod hΓ [F1] L5430 [F219]
  rw [show [F1] ++ L5430 ++ [F219] = L5428 from rfl, show [F1] ++ L5430 = L5425 from rfl,
    show L5430 ++ [F219] = L5427 from rfl] at h
  rw [i3065 hinj, i3063 hinj, i3064 hinj, i3066 hinj] at h
  linarith

theorem row1107 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1894 + (1 : ℝ) * HLm Γ 5 L5432 + (-1 : ℝ) * HLm Γ 5 L5434 + (-1 : ℝ) * HLm Γ 5 L5436 := by
  have h := HLm_submod hΓ [F1] L5437 [F214]
  rw [show [F1] ++ L5437 ++ [F214] = L5435 from rfl, show [F1] ++ L5437 = L5431 from rfl,
    show L5437 ++ [F214] = L5433 from rfl] at h
  rw [i3069 hinj, i3067 hinj, i3068 hinj, i3070 hinj] at h
  linarith

theorem row1108 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5438 + (1 : ℝ) * HLm Γ 5 L5440 + (-1 : ℝ) * HLm Γ 5 L5442 + (-1 : ℝ) * HLm Γ 5 L597 := by
  have h := HLm_submod hΓ [F210] L597 [F25]
  rw [show [F210] ++ L597 ++ [F25] = L5443 from rfl, show [F210] ++ L597 = L5439 from rfl,
    show L597 ++ [F25] = L5441 from rfl] at h
  rw [i3073 hinj, i3071 hinj, i3072 hinj] at h
  linarith

theorem row1109 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5444 + (1 : ℝ) * HLm Γ 5 L5446 + (-1 : ℝ) * HLm Γ 5 L5448 + (-1 : ℝ) * HLm Γ 5 L957 := by
  have h := HLm_submod hΓ [F210] L5450 [F36]
  rw [show [F210] ++ L5450 ++ [F36] = L5449 from rfl, show [F210] ++ L5450 = L5445 from rfl,
    show L5450 ++ [F36] = L5447 from rfl] at h
  rw [i3076 hinj, i3074 hinj, i3075 hinj, i3077 hinj] at h
  linarith

theorem row1110 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5451 + (1 : ℝ) * HLm Γ 5 L5453 + (-1 : ℝ) * HLm Γ 5 L5455 + (-1 : ℝ) * HLm Γ 5 L1332 := by
  have h := HLm_submod hΓ [F210] L5457 [F25]
  rw [show [F210] ++ L5457 ++ [F25] = L5456 from rfl, show [F210] ++ L5457 = L5452 from rfl,
    show L5457 ++ [F25] = L5454 from rfl] at h
  rw [i3080 hinj, i3078 hinj, i3079 hinj, i3081 hinj] at h
  linarith

theorem row1111 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1420 + (1 : ℝ) * HLm Γ 5 L5459 + (-1 : ℝ) * HLm Γ 5 L5461 + (-1 : ℝ) * HLm Γ 5 L5463 := by
  have h := HLm_submod hΓ [F7] L5464 [F236]
  rw [show [F7] ++ L5464 ++ [F236] = L5462 from rfl, show [F7] ++ L5464 = L5458 from rfl,
    show L5464 ++ [F236] = L5460 from rfl] at h
  rw [i3084 hinj, i3082 hinj, i3083 hinj, i3085 hinj] at h
  linarith

theorem row1112 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5465 + (1 : ℝ) * HLm Γ 5 L5327 + (-1 : ℝ) * HLm Γ 5 L5468 + (-1 : ℝ) * HLm Γ 5 L5470 := by
  have h := HLm_submod hΓ [F7] L5471 [F219]
  rw [show [F7] ++ L5471 ++ [F219] = L5469 from rfl, show [F7] ++ L5471 = L5466 from rfl,
    show L5471 ++ [F219] = L5467 from rfl] at h
  rw [i3088 hinj, i3086 hinj, i3087 hinj, i3089 hinj] at h
  linarith

theorem row1113 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5472 + (1 : ℝ) * HLm Γ 5 L5474 + (-1 : ℝ) * HLm Γ 5 L5476 + (-1 : ℝ) * HLm Γ 5 L5478 := by
  have h := HLm_submod hΓ [F210] L5479 [F90]
  rw [show [F210] ++ L5479 ++ [F90] = L5477 from rfl, show [F210] ++ L5479 = L5473 from rfl,
    show L5479 ++ [F90] = L5475 from rfl] at h
  rw [i3092 hinj, i3090 hinj, i3091 hinj, i3093 hinj] at h
  linarith

theorem row1114 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5480 + (1 : ℝ) * HLm Γ 5 L4289 + (-1 : ℝ) * HLm Γ 5 L5483 + (-1 : ℝ) * HLm Γ 5 L4285 := by
  have h := HLm_submod hΓ [F107] L5485 [F210]
  rw [show [F107] ++ L5485 ++ [F210] = L5484 from rfl, show [F107] ++ L5485 = L5481 from rfl,
    show L5485 ++ [F210] = L5482 from rfl] at h
  rw [i3096 hinj, i3094 hinj, i3095 hinj, i3097 hinj] at h
  linarith

theorem row1115 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L847 + (1 : ℝ) * HLm Γ 5 L5487 + (-1 : ℝ) * HLm Γ 5 L5489 + (-1 : ℝ) * HLm Γ 5 L989 := by
  have h := HLm_submod hΓ [F7] L1300 [F210]
  rw [show [F7] ++ L1300 ++ [F210] = L5490 from rfl, show [F7] ++ L1300 = L5486 from rfl,
    show L1300 ++ [F210] = L5488 from rfl] at h
  rw [i3100 hinj, i3098 hinj, i3099 hinj, i639 hinj] at h
  linarith

theorem row1116 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5491 + (1 : ℝ) * HLm Γ 5 L5493 + (-1 : ℝ) * HLm Γ 5 L5495 + (-1 : ℝ) * HLm Γ 5 L5497 := by
  have h := HLm_submod hΓ [F7] L5498 [F218]
  rw [show [F7] ++ L5498 ++ [F218] = L5496 from rfl, show [F7] ++ L5498 = L5492 from rfl,
    show L5498 ++ [F218] = L5494 from rfl] at h
  rw [i3103 hinj, i3101 hinj, i3102 hinj, i3104 hinj] at h
  linarith

theorem row1117 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1278 + (1 : ℝ) * HLm Γ 5 L5500 + (-1 : ℝ) * HLm Γ 5 L5502 + (-1 : ℝ) * HLm Γ 5 L5504 := by
  have h := HLm_submod hΓ [F1] L5505 [F228]
  rw [show [F1] ++ L5505 ++ [F228] = L5503 from rfl, show [F1] ++ L5505 = L5499 from rfl,
    show L5505 ++ [F228] = L5501 from rfl] at h
  rw [i3107 hinj, i3105 hinj, i3106 hinj, i3108 hinj] at h
  linarith

theorem row1118 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5506 + (1 : ℝ) * HLm Γ 5 L5508 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5511 := by
  have h := HLm_submod hΓ [F7] L5512 [F4]
  rw [show [F7] ++ L5512 ++ [F4] = L5510 from rfl, show [F7] ++ L5512 = L5507 from rfl,
    show L5512 ++ [F4] = L5509 from rfl] at h
  rw [i3111 hinj, i3109 hinj, i3110 hinj, i3112 hinj] at h
  linarith

theorem row1119 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1420 + (1 : ℝ) * HLm Γ 5 L4245 + (-1 : ℝ) * HLm Γ 5 L5515 + (-1 : ℝ) * HLm Γ 5 L4243 := by
  have h := HLm_submod hΓ [F7] L4244 [F210]
  rw [show [F7] ++ L4244 ++ [F210] = L5516 from rfl, show [F7] ++ L4244 = L5513 from rfl,
    show L4244 ++ [F210] = L5514 from rfl] at h
  rw [i3115 hinj, i3113 hinj, i3114 hinj, i2373 hinj] at h
  linarith

theorem row1120 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1278 + (1 : ℝ) * HLm Γ 5 L5192 + (-1 : ℝ) * HLm Γ 5 L5502 + (-1 : ℝ) * HLm Γ 5 L5520 := by
  have h := HLm_submod hΓ [F1] L5521 [F228]
  rw [show [F1] ++ L5521 ++ [F228] = L5519 from rfl, show [F1] ++ L5521 = L5517 from rfl,
    show L5521 ++ [F228] = L5518 from rfl] at h
  rw [i3118 hinj, i3116 hinj, i3117 hinj, i3119 hinj] at h
  linarith

theorem row1121 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4842 + (1 : ℝ) * HLm Γ 5 L5226 + (-1 : ℝ) * HLm Γ 5 L5524 + (-1 : ℝ) * HLm Γ 5 L3883 := by
  have h := HLm_submod hΓ [F7] L5526 [F33]
  rw [show [F7] ++ L5526 ++ [F33] = L5525 from rfl, show [F7] ++ L5526 = L5522 from rfl,
    show L5526 ++ [F33] = L5523 from rfl] at h
  rw [i3122 hinj, i3120 hinj, i3121 hinj, i3123 hinj] at h
  linarith

theorem row1122 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4455 + (1 : ℝ) * HLm Γ 5 L4720 + (-1 : ℝ) * HLm Γ 5 L5529 + (-1 : ℝ) * HLm Γ 5 L3914 := by
  have h := HLm_submod hΓ [F7] L5531 [F1]
  rw [show [F7] ++ L5531 ++ [F1] = L5530 from rfl, show [F7] ++ L5531 = L5527 from rfl,
    show L5531 ++ [F1] = L5528 from rfl] at h
  rw [i3126 hinj, i3124 hinj, i3125 hinj, i3127 hinj] at h
  linarith

theorem row1123 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5532 + (1 : ℝ) * HLm Γ 5 L5534 + (-1 : ℝ) * HLm Γ 5 L5536 + (-1 : ℝ) * HLm Γ 5 L5538 := by
  have h := HLm_submod hΓ [F7] L5539 [F33]
  rw [show [F7] ++ L5539 ++ [F33] = L5537 from rfl, show [F7] ++ L5539 = L5533 from rfl,
    show L5539 ++ [F33] = L5535 from rfl] at h
  rw [i3130 hinj, i3128 hinj, i3129 hinj, i3131 hinj] at h
  linarith

theorem row1124 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5540 + (1 : ℝ) * HLm Γ 5 L4265 + (-1 : ℝ) * HLm Γ 5 L5543 + (-1 : ℝ) * HLm Γ 5 L4263 := by
  have h := HLm_submod hΓ [F3] L5545 [F210]
  rw [show [F3] ++ L5545 ++ [F210] = L5544 from rfl, show [F3] ++ L5545 = L5541 from rfl,
    show L5545 ++ [F210] = L5542 from rfl] at h
  rw [i3134 hinj, i3132 hinj, i3133 hinj, i3135 hinj] at h
  linarith

theorem row1125 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4842 + (1 : ℝ) * HLm Γ 5 L4270 + (-1 : ℝ) * HLm Γ 5 L5524 + (-1 : ℝ) * HLm Γ 5 L5549 := by
  have h := HLm_submod hΓ [F7] L5550 [F33]
  rw [show [F7] ++ L5550 ++ [F33] = L5548 from rfl, show [F7] ++ L5550 = L5546 from rfl,
    show L5550 ++ [F33] = L5547 from rfl] at h
  rw [i3138 hinj, i3136 hinj, i3137 hinj, i3139 hinj] at h
  linarith

theorem row1126 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5551 + (1 : ℝ) * HLm Γ 5 L5553 + (-1 : ℝ) * HLm Γ 5 L5555 + (-1 : ℝ) * HLm Γ 5 L4268 := by
  have h := HLm_submod hΓ [F44] L5557 [F210]
  rw [show [F44] ++ L5557 ++ [F210] = L5556 from rfl, show [F44] ++ L5557 = L5552 from rfl,
    show L5557 ++ [F210] = L5554 from rfl] at h
  rw [i3142 hinj, i3140 hinj, i3141 hinj, i3143 hinj] at h
  linarith

theorem row1127 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1278 + (1 : ℝ) * HLm Γ 5 L5559 + (-1 : ℝ) * HLm Γ 5 L5502 + (-1 : ℝ) * HLm Γ 5 L5562 := by
  have h := HLm_submod hΓ [F1] L5563 [F228]
  rw [show [F1] ++ L5563 ++ [F228] = L5561 from rfl, show [F1] ++ L5563 = L5558 from rfl,
    show L5563 ++ [F228] = L5560 from rfl] at h
  rw [i3146 hinj, i3144 hinj, i3145 hinj, i3147 hinj] at h
  linarith

theorem row1128 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5564 + (1 : ℝ) * HLm Γ 5 L5566 + (-1 : ℝ) * HLm Γ 5 L5568 + (-1 : ℝ) * HLm Γ 5 L5570 := by
  have h := HLm_submod hΓ [F7] L5571 [F6]
  rw [show [F7] ++ L5571 ++ [F6] = L5569 from rfl, show [F7] ++ L5571 = L5565 from rfl,
    show L5571 ++ [F6] = L5567 from rfl] at h
  rw [i3150 hinj, i3148 hinj, i3149 hinj, i3151 hinj] at h
  linarith

theorem row1129 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5572 + (1 : ℝ) * HLm Γ 5 L5574 + (-1 : ℝ) * HLm Γ 5 L5576 + (-1 : ℝ) * HLm Γ 5 L1835 := by
  have h := HLm_submod hΓ [F210] L1836 [F25]
  rw [show [F210] ++ L1836 ++ [F25] = L5577 from rfl, show [F210] ++ L1836 = L5573 from rfl,
    show L1836 ++ [F25] = L5575 from rfl] at h
  rw [i3154 hinj, i3152 hinj, i3153 hinj, i983 hinj] at h
  linarith

theorem row1130 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4562 + (1 : ℝ) * HLm Γ 5 L5579 + (-1 : ℝ) * HLm Γ 5 L5581 + (-1 : ℝ) * HLm Γ 5 L5365 := by
  have h := HLm_submod hΓ [F7] L5583 [F33]
  rw [show [F7] ++ L5583 ++ [F33] = L5582 from rfl, show [F7] ++ L5583 = L5578 from rfl,
    show L5583 ++ [F33] = L5580 from rfl] at h
  rw [i3157 hinj, i3155 hinj, i3156 hinj, i3158 hinj] at h
  linarith

theorem row1131 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L842 + (1 : ℝ) * HLm Γ 5 L4313 + (-1 : ℝ) * HLm Γ 5 L5381 + (-1 : ℝ) * HLm Γ 5 L4309 := by
  have h := HLm_submod hΓ [F0] L5587 [F210]
  rw [show [F0] ++ L5587 ++ [F210] = L5586 from rfl, show [F0] ++ L5587 = L5584 from rfl,
    show L5587 ++ [F210] = L5585 from rfl] at h
  rw [i3161 hinj, i3159 hinj, i3160 hinj, i3162 hinj] at h
  linarith

theorem row1132 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L842 + (1 : ℝ) * HLm Γ 5 L4324 + (-1 : ℝ) * HLm Γ 5 L5381 + (-1 : ℝ) * HLm Γ 5 L4320 := by
  have h := HLm_submod hΓ [F0] L5591 [F210]
  rw [show [F0] ++ L5591 ++ [F210] = L5590 from rfl, show [F0] ++ L5591 = L5588 from rfl,
    show L5591 ++ [F210] = L5589 from rfl] at h
  rw [i3165 hinj, i3163 hinj, i3164 hinj, i3166 hinj] at h
  linarith

theorem row1133 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4317 + (1 : ℝ) * HLm Γ 5 L4756 + (-1 : ℝ) * HLm Γ 5 L4558 + (-1 : ℝ) * HLm Γ 5 L3309 := by
  have h := HLm_submod hΓ [F0] L5595 [F2]
  rw [show [F0] ++ L5595 ++ [F2] = L5594 from rfl, show [F0] ++ L5595 = L5592 from rfl,
    show L5595 ++ [F2] = L5593 from rfl] at h
  rw [i3169 hinj, i3167 hinj, i3168 hinj, i3170 hinj] at h
  linarith

theorem row1134 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5596 + (1 : ℝ) * HLm Γ 5 L5598 + (-1 : ℝ) * HLm Γ 5 L5600 + (-1 : ℝ) * HLm Γ 5 L5602 := by
  have h := HLm_submod hΓ [F210] L5603 [F27]
  rw [show [F210] ++ L5603 ++ [F27] = L5601 from rfl, show [F210] ++ L5603 = L5597 from rfl,
    show L5603 ++ [F27] = L5599 from rfl] at h
  rw [i3173 hinj, i3171 hinj, i3172 hinj, i3174 hinj] at h
  linarith

theorem row1135 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L4343 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L4339 := by
  have h := HLm_submod hΓ [F10] L5607 [F210]
  rw [show [F10] ++ L5607 ++ [F210] = L5606 from rfl, show [F10] ++ L5607 = L5604 from rfl,
    show L5607 ++ [F210] = L5605 from rfl] at h
  rw [i3177 hinj, i3175 hinj, i3176 hinj, i3178 hinj] at h
  linarith

theorem row1136 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L4336 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L4332 := by
  have h := HLm_submod hΓ [F10] L5611 [F210]
  rw [show [F10] ++ L5611 ++ [F210] = L5610 from rfl, show [F10] ++ L5611 = L5608 from rfl,
    show L5611 ++ [F210] = L5609 from rfl] at h
  rw [i3181 hinj, i3179 hinj, i3180 hinj, i3182 hinj] at h
  linarith

theorem row1137 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5612 + (1 : ℝ) * HLm Γ 5 L5614 + (-1 : ℝ) * HLm Γ 5 L5616 + (-1 : ℝ) * HLm Γ 5 L5618 := by
  have h := HLm_submod hΓ [F2] L5619 [F27]
  rw [show [F2] ++ L5619 ++ [F27] = L5617 from rfl, show [F2] ++ L5619 = L5613 from rfl,
    show L5619 ++ [F27] = L5615 from rfl] at h
  rw [i3185 hinj, i3183 hinj, i3184 hinj, i3186 hinj] at h
  linarith

theorem row1138 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1894 + (1 : ℝ) * HLm Γ 5 L4624 + (-1 : ℝ) * HLm Γ 5 L1044 + (-1 : ℝ) * HLm Γ 5 L5623 := by
  have h := HLm_submod hΓ [F0] L5624 [F2]
  rw [show [F0] ++ L5624 ++ [F2] = L5622 from rfl, show [F0] ++ L5624 = L5620 from rfl,
    show L5624 ++ [F2] = L5621 from rfl] at h
  rw [i3189 hinj, i3187 hinj, i3188 hinj, i3190 hinj] at h
  linarith

theorem row1139 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4358 + (1 : ℝ) * HLm Γ 5 L5626 + (-1 : ℝ) * HLm Γ 5 L5628 + (-1 : ℝ) * HLm Γ 5 L4356 := by
  have h := HLm_submod hΓ [F2] L5630 [F211]
  rw [show [F2] ++ L5630 ++ [F211] = L5629 from rfl, show [F2] ++ L5630 = L5625 from rfl,
    show L5630 ++ [F211] = L5627 from rfl] at h
  rw [i3193 hinj, i3191 hinj, i3192 hinj, i3194 hinj] at h
  linarith

theorem row1140 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L5632 + (-1 : ℝ) * HLm Γ 5 L4558 + (-1 : ℝ) * HLm Γ 5 L1438 := by
  have h := HLm_submod hΓ [F0] L5635 [F219]
  rw [show [F0] ++ L5635 ++ [F219] = L5634 from rfl, show [F0] ++ L5635 = L5631 from rfl,
    show L5635 ++ [F219] = L5633 from rfl] at h
  rw [i3197 hinj, i3195 hinj, i3196 hinj, i3198 hinj] at h
  linarith

theorem row1141 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1719 + (1 : ℝ) * HLm Γ 5 L5637 + (-1 : ℝ) * HLm Γ 5 L5639 + (-1 : ℝ) * HLm Γ 5 L1219 := by
  have h := HLm_submod hΓ [F1] L1219 [F211]
  rw [show [F1] ++ L1219 ++ [F211] = L5640 from rfl, show [F1] ++ L1219 = L5636 from rfl,
    show L1219 ++ [F211] = L5638 from rfl] at h
  rw [i3201 hinj, i3199 hinj, i3200 hinj] at h
  linarith

theorem row1142 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L847 + (1 : ℝ) * HLm Γ 5 L5642 + (-1 : ℝ) * HLm Γ 5 L5489 + (-1 : ℝ) * HLm Γ 5 L5645 := by
  have h := HLm_submod hΓ [F0] L5646 [F210]
  rw [show [F0] ++ L5646 ++ [F210] = L5644 from rfl, show [F0] ++ L5646 = L5641 from rfl,
    show L5646 ++ [F210] = L5643 from rfl] at h
  rw [i3204 hinj, i3202 hinj, i3203 hinj, i3205 hinj] at h
  linarith

theorem row1143 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5647 + (1 : ℝ) * HLm Γ 5 L5649 + (-1 : ℝ) * HLm Γ 5 L5651 + (-1 : ℝ) * HLm Γ 5 L5653 := by
  have h := HLm_submod hΓ [F210] L5654 [F86]
  rw [show [F210] ++ L5654 ++ [F86] = L5652 from rfl, show [F210] ++ L5654 = L5648 from rfl,
    show L5654 ++ [F86] = L5650 from rfl] at h
  rw [i3208 hinj, i3206 hinj, i3207 hinj, i3209 hinj] at h
  linarith

theorem row1144 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5655 + (1 : ℝ) * HLm Γ 5 L4372 + (-1 : ℝ) * HLm Γ 5 L5658 + (-1 : ℝ) * HLm Γ 5 L4370 := by
  have h := HLm_submod hΓ [F47] L4371 [F210]
  rw [show [F47] ++ L4371 ++ [F210] = L5659 from rfl, show [F47] ++ L4371 = L5656 from rfl,
    show L4371 ++ [F210] = L5657 from rfl] at h
  rw [i3212 hinj, i3210 hinj, i3211 hinj, i2450 hinj] at h
  linarith

theorem row1145 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4379 + (1 : ℝ) * HLm Γ 5 L5661 + (-1 : ℝ) * HLm Γ 5 L5663 + (-1 : ℝ) * HLm Γ 5 L4377 := by
  have h := HLm_submod hΓ [F210] L5665 [F86]
  rw [show [F210] ++ L5665 ++ [F86] = L5664 from rfl, show [F210] ++ L5665 = L5660 from rfl,
    show L5665 ++ [F86] = L5662 from rfl] at h
  rw [i3215 hinj, i3213 hinj, i3214 hinj, i3216 hinj] at h
  linarith

theorem row1146 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1614 + (1 : ℝ) * HLm Γ 5 L4389 + (-1 : ℝ) * HLm Γ 5 L5668 + (-1 : ℝ) * HLm Γ 5 L4385 := by
  have h := HLm_submod hΓ [F0] L5670 [F214]
  rw [show [F0] ++ L5670 ++ [F214] = L5669 from rfl, show [F0] ++ L5670 = L5666 from rfl,
    show L5670 ++ [F214] = L5667 from rfl] at h
  rw [i3219 hinj, i3217 hinj, i3218 hinj, i3220 hinj] at h
  linarith

theorem row1147 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L5672 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5675 := by
  have h := HLm_submod hΓ [F12] L5676 [F210]
  rw [show [F12] ++ L5676 ++ [F210] = L5674 from rfl, show [F12] ++ L5676 = L5671 from rfl,
    show L5676 ++ [F210] = L5673 from rfl] at h
  rw [i3223 hinj, i3221 hinj, i3222 hinj, i3224 hinj] at h
  linarith

theorem row1148 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5677 + (1 : ℝ) * HLm Γ 5 L5679 + (-1 : ℝ) * HLm Γ 5 L5681 + (-1 : ℝ) * HLm Γ 5 L5683 := by
  have h := HLm_submod hΓ [F210] L5684 [F43]
  rw [show [F210] ++ L5684 ++ [F43] = L5682 from rfl, show [F210] ++ L5684 = L5678 from rfl,
    show L5684 ++ [F43] = L5680 from rfl] at h
  rw [i3227 hinj, i3225 hinj, i3226 hinj, i3228 hinj] at h
  linarith

theorem row1149 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5685 + (1 : ℝ) * HLm Γ 5 L5687 + (-1 : ℝ) * HLm Γ 5 L5689 + (-1 : ℝ) * HLm Γ 5 L5691 := by
  have h := HLm_submod hΓ [F210] L5692 [F36]
  rw [show [F210] ++ L5692 ++ [F36] = L5690 from rfl, show [F210] ++ L5692 = L5686 from rfl,
    show L5692 ++ [F36] = L5688 from rfl] at h
  rw [i3231 hinj, i3229 hinj, i3230 hinj, i3232 hinj] at h
  linarith

theorem row1150 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5693 + (1 : ℝ) * HLm Γ 5 L5695 + (-1 : ℝ) * HLm Γ 5 L5697 + (-1 : ℝ) * HLm Γ 5 L2572 := by
  have h := HLm_submod hΓ [F210] L2573 [F36]
  rw [show [F210] ++ L2573 ++ [F36] = L5698 from rfl, show [F210] ++ L2573 = L5694 from rfl,
    show L2573 ++ [F36] = L5696 from rfl] at h
  rw [i3235 hinj, i3233 hinj, i3234 hinj, i1434 hinj] at h
  linarith

theorem row1151 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L5700 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L1710 := by
  have h := HLm_submod hΓ [F111] L5703 [F210]
  rw [show [F111] ++ L5703 ++ [F210] = L5702 from rfl, show [F111] ++ L5703 = L5699 from rfl,
    show L5703 ++ [F210] = L5701 from rfl] at h
  rw [i3238 hinj, i3236 hinj, i3237 hinj, i3239 hinj] at h
  linarith

theorem row1152 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L5705 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L1728 := by
  have h := HLm_submod hΓ [F111] L5708 [F210]
  rw [show [F111] ++ L5708 ++ [F210] = L5707 from rfl, show [F111] ++ L5708 = L5704 from rfl,
    show L5708 ++ [F210] = L5706 from rfl] at h
  rw [i3242 hinj, i3240 hinj, i3241 hinj, i3243 hinj] at h
  linarith

theorem row1153 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5709 + (1 : ℝ) * HLm Γ 5 L5711 + (-1 : ℝ) * HLm Γ 5 L5713 + (-1 : ℝ) * HLm Γ 5 L5715 := by
  have h := HLm_submod hΓ [F210] L5716 [F86]
  rw [show [F210] ++ L5716 ++ [F86] = L5714 from rfl, show [F210] ++ L5716 = L5710 from rfl,
    show L5716 ++ [F86] = L5712 from rfl] at h
  rw [i3246 hinj, i3244 hinj, i3245 hinj, i3247 hinj] at h
  linarith

theorem row1154 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4406 + (1 : ℝ) * HLm Γ 5 L4980 + (-1 : ℝ) * HLm Γ 5 L5719 + (-1 : ℝ) * HLm Γ 5 L4398 := by
  have h := HLm_submod hΓ [F1] L4399 [F67]
  rw [show [F1] ++ L4399 ++ [F67] = L5720 from rfl, show [F1] ++ L4399 = L5717 from rfl,
    show L4399 ++ [F67] = L5718 from rfl] at h
  rw [i3250 hinj, i3248 hinj, i3249 hinj, i2466 hinj] at h
  linarith

theorem row1155 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4448 + (1 : ℝ) * HLm Γ 5 L5722 + (-1 : ℝ) * HLm Γ 5 L5724 + (-1 : ℝ) * HLm Γ 5 L1664 := by
  have h := HLm_submod hΓ [F210] L5726 [F86]
  rw [show [F210] ++ L5726 ++ [F86] = L5725 from rfl, show [F210] ++ L5726 = L5721 from rfl,
    show L5726 ++ [F86] = L5723 from rfl] at h
  rw [i3253 hinj, i3251 hinj, i3252 hinj, i3254 hinj] at h
  linarith

theorem row1156 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5465 + (1 : ℝ) * HLm Γ 5 L5728 + (-1 : ℝ) * HLm Γ 5 L5730 + (-1 : ℝ) * HLm Γ 5 L4477 := by
  have h := HLm_submod hΓ [F0] L5732 [F214]
  rw [show [F0] ++ L5732 ++ [F214] = L5731 from rfl, show [F0] ++ L5732 = L5727 from rfl,
    show L5732 ++ [F214] = L5729 from rfl] at h
  rw [i3257 hinj, i3255 hinj, i3256 hinj, i3258 hinj] at h
  linarith

theorem row1157 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5733 + (1 : ℝ) * HLm Γ 5 L5735 + (-1 : ℝ) * HLm Γ 5 L5515 + (-1 : ℝ) * HLm Γ 5 L4418 := by
  have h := HLm_submod hΓ [F0] L5738 [F16]
  rw [show [F0] ++ L5738 ++ [F16] = L5737 from rfl, show [F0] ++ L5738 = L5734 from rfl,
    show L5738 ++ [F16] = L5736 from rfl] at h
  rw [i3261 hinj, i3259 hinj, i3260 hinj, i3262 hinj] at h
  linarith

theorem row1158 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5739 + (1 : ℝ) * HLm Γ 5 L5108 + (-1 : ℝ) * HLm Γ 5 L5489 + (-1 : ℝ) * HLm Γ 5 L5105 := by
  have h := HLm_submod hΓ [F0] L5105 [F2]
  rw [show [F0] ++ L5105 ++ [F2] = L5740 from rfl, show [F0] ++ L5105 = L5739 from rfl,
    show L5105 ++ [F2] = L5109 from rfl] at h
  rw [i3263 hinj, i2877 hinj] at h
  linarith

theorem row1159 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5739 + (1 : ℝ) * HLm Γ 5 L5742 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5745 := by
  have h := HLm_submod hΓ [F0] L5746 [F4]
  rw [show [F0] ++ L5746 ++ [F4] = L5744 from rfl, show [F0] ++ L5746 = L5741 from rfl,
    show L5746 ++ [F4] = L5743 from rfl] at h
  rw [i3266 hinj, i3264 hinj, i3265 hinj, i3267 hinj] at h
  linarith

theorem row1160 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5747 + (1 : ℝ) * HLm Γ 5 L5749 + (-1 : ℝ) * HLm Γ 5 L5751 + (-1 : ℝ) * HLm Γ 5 L5753 := by
  have h := HLm_submod hΓ [F0] L5754 [F3]
  rw [show [F0] ++ L5754 ++ [F3] = L5752 from rfl, show [F0] ++ L5754 = L5748 from rfl,
    show L5754 ++ [F3] = L5750 from rfl] at h
  rw [i3270 hinj, i3268 hinj, i3269 hinj, i3271 hinj] at h
  linarith

theorem row1161 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5755 + (1 : ℝ) * HLm Γ 5 L5757 + (-1 : ℝ) * HLm Γ 5 L5759 + (-1 : ℝ) * HLm Γ 5 L1161 := by
  have h := HLm_submod hΓ [F1] L5761 [F217]
  rw [show [F1] ++ L5761 ++ [F217] = L5760 from rfl, show [F1] ++ L5761 = L5756 from rfl,
    show L5761 ++ [F217] = L5758 from rfl] at h
  rw [i3274 hinj, i3272 hinj, i3273 hinj, i3275 hinj] at h
  linarith

theorem row1162 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5762 + (1 : ℝ) * HLm Γ 5 L5764 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5767 := by
  have h := HLm_submod hΓ [F0] L5768 [F108]
  rw [show [F0] ++ L5768 ++ [F108] = L5766 from rfl, show [F0] ++ L5768 = L5763 from rfl,
    show L5768 ++ [F108] = L5765 from rfl] at h
  rw [i3278 hinj, i3276 hinj, i3277 hinj, i3279 hinj] at h
  linarith

theorem row1163 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5769 + (1 : ℝ) * HLm Γ 5 L5771 + (-1 : ℝ) * HLm Γ 5 L5773 + (-1 : ℝ) * HLm Γ 5 L5775 := by
  have h := HLm_submod hΓ [F12] L5776 [F210]
  rw [show [F12] ++ L5776 ++ [F210] = L5774 from rfl, show [F12] ++ L5776 = L5770 from rfl,
    show L5776 ++ [F210] = L5772 from rfl] at h
  rw [i3282 hinj, i3280 hinj, i3281 hinj, i3283 hinj] at h
  linarith

theorem row1164 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4461 + (1 : ℝ) * HLm Γ 5 L5777 + (-1 : ℝ) * HLm Γ 5 L5719 + (-1 : ℝ) * HLm Γ 5 L4459 := by
  have h := HLm_submod hΓ [F1] L4460 [F12]
  rw [show [F1] ++ L4460 ++ [F12] = L5779 from rfl, show [F1] ++ L4460 = L4462 from rfl,
    show L4460 ++ [F12] = L5778 from rfl] at h
  rw [i3285 hinj, i2503 hinj, i3284 hinj, i2502 hinj] at h
  linarith

theorem row1165 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5780 + (1 : ℝ) * HLm Γ 5 L4495 + (-1 : ℝ) * HLm Γ 5 L5783 + (-1 : ℝ) * HLm Γ 5 L4479 := by
  have h := HLm_submod hΓ [F0] L5785 [F43]
  rw [show [F0] ++ L5785 ++ [F43] = L5784 from rfl, show [F0] ++ L5785 = L5781 from rfl,
    show L5785 ++ [F43] = L5782 from rfl] at h
  rw [i3288 hinj, i3286 hinj, i3287 hinj, i3289 hinj] at h
  linarith

theorem row1166 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5786 + (1 : ℝ) * HLm Γ 5 L4475 + (-1 : ℝ) * HLm Γ 5 L5789 + (-1 : ℝ) * HLm Γ 5 L4485 := by
  have h := HLm_submod hΓ [F0] L5791 [F34]
  rw [show [F0] ++ L5791 ++ [F34] = L5790 from rfl, show [F0] ++ L5791 = L5787 from rfl,
    show L5791 ++ [F34] = L5788 from rfl] at h
  rw [i3292 hinj, i3290 hinj, i3291 hinj, i3293 hinj] at h
  linarith

theorem row1167 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4503 + (1 : ℝ) * HLm Γ 5 L5793 + (-1 : ℝ) * HLm Γ 5 L5795 + (-1 : ℝ) * HLm Γ 5 L4501 := by
  have h := HLm_submod hΓ [F0] L5797 [F214]
  rw [show [F0] ++ L5797 ++ [F214] = L5796 from rfl, show [F0] ++ L5797 = L5792 from rfl,
    show L5797 ++ [F214] = L5794 from rfl] at h
  rw [i3296 hinj, i3294 hinj, i3295 hinj, i3297 hinj] at h
  linarith

theorem row1168 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5798 + (1 : ℝ) * HLm Γ 5 L5800 + (-1 : ℝ) * HLm Γ 5 L5802 + (-1 : ℝ) * HLm Γ 5 L4486 := by
  have h := HLm_submod hΓ [F210] L5804 [F33]
  rw [show [F210] ++ L5804 ++ [F33] = L5803 from rfl, show [F210] ++ L5804 = L5799 from rfl,
    show L5804 ++ [F33] = L5801 from rfl] at h
  rw [i3300 hinj, i3298 hinj, i3299 hinj, i3301 hinj] at h
  linarith

theorem row1169 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5805 + (1 : ℝ) * HLm Γ 5 L5807 + (-1 : ℝ) * HLm Γ 5 L5809 + (-1 : ℝ) * HLm Γ 5 L4493 := by
  have h := HLm_submod hΓ [F210] L5811 [F30]
  rw [show [F210] ++ L5811 ++ [F30] = L5810 from rfl, show [F210] ++ L5811 = L5806 from rfl,
    show L5811 ++ [F30] = L5808 from rfl] at h
  rw [i3304 hinj, i3302 hinj, i3303 hinj, i3305 hinj] at h
  linarith

theorem row1170 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4298 + (1 : ℝ) * HLm Γ 5 L4540 + (-1 : ℝ) * HLm Γ 5 L5814 + (-1 : ℝ) * HLm Γ 5 L4516 := by
  have h := HLm_submod hΓ [F0] L5816 [F55]
  rw [show [F0] ++ L5816 ++ [F55] = L5815 from rfl, show [F0] ++ L5816 = L5812 from rfl,
    show L5816 ++ [F55] = L5813 from rfl] at h
  rw [i3308 hinj, i3306 hinj, i3307 hinj, i3309 hinj] at h
  linarith

theorem row1171 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4511 + (1 : ℝ) * HLm Γ 5 L4420 + (-1 : ℝ) * HLm Γ 5 L5819 + (-1 : ℝ) * HLm Γ 5 L4509 := by
  have h := HLm_submod hΓ [F0] L5821 [F3]
  rw [show [F0] ++ L5821 ++ [F3] = L5820 from rfl, show [F0] ++ L5821 = L5817 from rfl,
    show L5821 ++ [F3] = L5818 from rfl] at h
  rw [i3312 hinj, i3310 hinj, i3311 hinj, i3313 hinj] at h
  linarith

theorem row1172 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4511 + (1 : ℝ) * HLm Γ 5 L4488 + (-1 : ℝ) * HLm Γ 5 L5823 + (-1 : ℝ) * HLm Γ 5 L4509 := by
  have h := HLm_submod hΓ [F0] L5821 [F23]
  rw [show [F0] ++ L5821 ++ [F23] = L5824 from rfl, show [F0] ++ L5821 = L5817 from rfl,
    show L5821 ++ [F23] = L5822 from rfl] at h
  rw [i3315 hinj, i3310 hinj, i3314 hinj, i3313 hinj] at h
  linarith

theorem row1173 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4818 + (1 : ℝ) * HLm Γ 5 L4552 + (-1 : ℝ) * HLm Γ 5 L5489 + (-1 : ℝ) * HLm Γ 5 L4550 := by
  have h := HLm_submod hΓ [F0] L5828 [F12]
  rw [show [F0] ++ L5828 ++ [F12] = L5827 from rfl, show [F0] ++ L5828 = L5825 from rfl,
    show L5828 ++ [F12] = L5826 from rfl] at h
  rw [i3318 hinj, i3316 hinj, i3317 hinj, i3319 hinj] at h
  linarith

theorem row1174 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4522 + (1 : ℝ) * HLm Γ 5 L5830 + (-1 : ℝ) * HLm Γ 5 L5832 + (-1 : ℝ) * HLm Γ 5 L4520 := by
  have h := HLm_submod hΓ [F0] L5834 [F3]
  rw [show [F0] ++ L5834 ++ [F3] = L5833 from rfl, show [F0] ++ L5834 = L5829 from rfl,
    show L5834 ++ [F3] = L5831 from rfl] at h
  rw [i3322 hinj, i3320 hinj, i3321 hinj, i3323 hinj] at h
  linarith

theorem row1175 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5835 + (1 : ℝ) * HLm Γ 5 L4527 + (-1 : ℝ) * HLm Γ 5 L5838 + (-1 : ℝ) * HLm Γ 5 L4525 := by
  have h := HLm_submod hΓ [F51] L5840 [F210]
  rw [show [F51] ++ L5840 ++ [F210] = L5839 from rfl, show [F51] ++ L5840 = L5836 from rfl,
    show L5840 ++ [F210] = L5837 from rfl] at h
  rw [i3326 hinj, i3324 hinj, i3325 hinj, i3327 hinj] at h
  linarith

theorem row1176 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L4533 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L1150 := by
  have h := HLm_submod hΓ [F4] L5844 [F210]
  rw [show [F4] ++ L5844 ++ [F210] = L5843 from rfl, show [F4] ++ L5844 = L5841 from rfl,
    show L5844 ++ [F210] = L5842 from rfl] at h
  rw [i3330 hinj, i3328 hinj, i3329 hinj, i3331 hinj] at h
  linarith

theorem row1177 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1832 + (1 : ℝ) * HLm Γ 5 L5846 + (-1 : ℝ) * HLm Γ 5 L5848 + (-1 : ℝ) * HLm Γ 5 L4538 := by
  have h := HLm_submod hΓ [F0] L5850 [F214]
  rw [show [F0] ++ L5850 ++ [F214] = L5849 from rfl, show [F0] ++ L5850 = L5845 from rfl,
    show L5850 ++ [F214] = L5847 from rfl] at h
  rw [i3334 hinj, i3332 hinj, i3333 hinj, i3335 hinj] at h
  linarith

theorem row1178 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5851 + (1 : ℝ) * HLm Γ 5 L4546 + (-1 : ℝ) * HLm Γ 5 L4558 + (-1 : ℝ) * HLm Γ 5 L4544 := by
  have h := HLm_submod hΓ [F1] L5855 [F0]
  rw [show [F1] ++ L5855 ++ [F0] = L5854 from rfl, show [F1] ++ L5855 = L5852 from rfl,
    show L5855 ++ [F0] = L5853 from rfl] at h
  rw [i3338 hinj, i3336 hinj, i3337 hinj, i3339 hinj] at h
  linarith

theorem row1179 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4695 + (1 : ℝ) * HLm Γ 5 L5857 + (-1 : ℝ) * HLm Γ 5 L5859 + (-1 : ℝ) * HLm Γ 5 L4556 := by
  have h := HLm_submod hΓ [F2] L5861 [F67]
  rw [show [F2] ++ L5861 ++ [F67] = L5860 from rfl, show [F2] ++ L5861 = L5856 from rfl,
    show L5861 ++ [F67] = L5858 from rfl] at h
  rw [i3342 hinj, i3340 hinj, i3341 hinj, i3343 hinj] at h
  linarith

theorem row1180 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5384 + (1 : ℝ) * HLm Γ 5 L5863 + (-1 : ℝ) * HLm Γ 5 L5381 + (-1 : ℝ) * HLm Γ 5 L5866 := by
  have h := HLm_submod hΓ [F0] L5867 [F45]
  rw [show [F0] ++ L5867 ++ [F45] = L5865 from rfl, show [F0] ++ L5867 = L5862 from rfl,
    show L5867 ++ [F45] = L5864 from rfl] at h
  rw [i3346 hinj, i3344 hinj, i3345 hinj, i3347 hinj] at h
  linarith

theorem row1181 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5384 + (1 : ℝ) * HLm Γ 5 L5869 + (-1 : ℝ) * HLm Γ 5 L5381 + (-1 : ℝ) * HLm Γ 5 L5872 := by
  have h := HLm_submod hΓ [F0] L5873 [F45]
  rw [show [F0] ++ L5873 ++ [F45] = L5871 from rfl, show [F0] ++ L5873 = L5868 from rfl,
    show L5873 ++ [F45] = L5870 from rfl] at h
  rw [i3350 hinj, i3348 hinj, i3349 hinj, i3351 hinj] at h
  linarith

theorem row1182 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5874 + (1 : ℝ) * HLm Γ 5 L5876 + (-1 : ℝ) * HLm Γ 5 L5878 + (-1 : ℝ) * HLm Γ 5 L5880 := by
  have h := HLm_submod hΓ [F210] L5881 [F36]
  rw [show [F210] ++ L5881 ++ [F36] = L5879 from rfl, show [F210] ++ L5881 = L5875 from rfl,
    show L5881 ++ [F36] = L5877 from rfl] at h
  rw [i3354 hinj, i3352 hinj, i3353 hinj, i3355 hinj] at h
  linarith

theorem row1183 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5882 + (1 : ℝ) * HLm Γ 5 L4586 + (-1 : ℝ) * HLm Γ 5 L5885 + (-1 : ℝ) * HLm Γ 5 L4604 := by
  have h := HLm_submod hΓ [F0] L5887 [F43]
  rw [show [F0] ++ L5887 ++ [F43] = L5886 from rfl, show [F0] ++ L5887 = L5883 from rfl,
    show L5887 ++ [F43] = L5884 from rfl] at h
  rw [i3358 hinj, i3356 hinj, i3357 hinj, i3359 hinj] at h
  linarith

theorem row1184 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4579 + (1 : ℝ) * HLm Γ 5 L4618 + (-1 : ℝ) * HLm Γ 5 L5889 + (-1 : ℝ) * HLm Γ 5 L3600 := by
  have h := HLm_submod hΓ [F0] L4578 [F16]
  rw [show [F0] ++ L4578 ++ [F16] = L5890 from rfl, show [F0] ++ L4578 = L4580 from rfl,
    show L4578 ++ [F16] = L5888 from rfl] at h
  rw [i3361 hinj, i2570 hinj, i3360 hinj, i2569 hinj] at h
  linarith

theorem row1185 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5891 + (1 : ℝ) * HLm Γ 5 L4613 + (-1 : ℝ) * HLm Γ 5 L5894 + (-1 : ℝ) * HLm Γ 5 L4584 := by
  have h := HLm_submod hΓ [F0] L5896 [F236]
  rw [show [F0] ++ L5896 ++ [F236] = L5895 from rfl, show [F0] ++ L5896 = L5892 from rfl,
    show L5896 ++ [F236] = L5893 from rfl] at h
  rw [i3364 hinj, i3362 hinj, i3363 hinj, i3365 hinj] at h
  linarith

theorem row1186 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1044 + (1 : ℝ) * HLm Γ 5 L5885 + (-1 : ℝ) * HLm Γ 5 L2831 + (-1 : ℝ) * HLm Γ 5 L5891 := by
  have h := HLm_submod hΓ [F1] L5900 [F210]
  rw [show [F1] ++ L5900 ++ [F210] = L5899 from rfl, show [F1] ++ L5900 = L5897 from rfl,
    show L5900 ++ [F210] = L5898 from rfl] at h
  rw [i3368 hinj, i3366 hinj, i3367 hinj, i3369 hinj] at h
  linarith

theorem row1187 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5901 + (1 : ℝ) * HLm Γ 5 L5903 + (-1 : ℝ) * HLm Γ 5 L5905 + (-1 : ℝ) * HLm Γ 5 L5907 := by
  have h := HLm_submod hΓ [F51] L5908 [F210]
  rw [show [F51] ++ L5908 ++ [F210] = L5906 from rfl, show [F51] ++ L5908 = L5902 from rfl,
    show L5908 ++ [F210] = L5904 from rfl] at h
  rw [i3372 hinj, i3370 hinj, i3371 hinj, i3373 hinj] at h
  linarith

theorem row1188 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L4630 + (1 : ℝ) * HLm Γ 5 L5910 + (-1 : ℝ) * HLm Γ 5 L5912 + (-1 : ℝ) * HLm Γ 5 L4628 := by
  have h := HLm_submod hΓ [F1] L5914 [F211]
  rw [show [F1] ++ L5914 ++ [F211] = L5913 from rfl, show [F1] ++ L5914 = L5909 from rfl,
    show L5914 ++ [F211] = L5911 from rfl] at h
  rw [i3376 hinj, i3374 hinj, i3375 hinj, i3377 hinj] at h
  linarith

theorem row1189 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5915 + (1 : ℝ) * HLm Γ 5 L5917 + (-1 : ℝ) * HLm Γ 5 L5919 + (-1 : ℝ) * HLm Γ 5 L4622 := by
  have h := HLm_submod hΓ [F210] L5921 [F17]
  rw [show [F210] ++ L5921 ++ [F17] = L5920 from rfl, show [F210] ++ L5921 = L5916 from rfl,
    show L5921 ++ [F17] = L5918 from rfl] at h
  rw [i3380 hinj, i3378 hinj, i3379 hinj, i3381 hinj] at h
  linarith

theorem row1190 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5922 + (1 : ℝ) * HLm Γ 5 L4586 + (-1 : ℝ) * HLm Γ 5 L5925 + (-1 : ℝ) * HLm Γ 5 L4606 := by
  have h := HLm_submod hΓ [F1] L4607 [F9]
  rw [show [F1] ++ L4607 ++ [F9] = L5926 from rfl, show [F1] ++ L4607 = L5923 from rfl,
    show L4607 ++ [F9] = L5924 from rfl] at h
  rw [i3384 hinj, i3382 hinj, i3383 hinj, i2586 hinj] at h
  linarith

theorem row1191 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5927 + (1 : ℝ) * HLm Γ 5 L5929 + (-1 : ℝ) * HLm Γ 5 L5931 + (-1 : ℝ) * HLm Γ 5 L4611 := by
  have h := HLm_submod hΓ [F1] L5933 [F7]
  rw [show [F1] ++ L5933 ++ [F7] = L5932 from rfl, show [F1] ++ L5933 = L5928 from rfl,
    show L5933 ++ [F7] = L5930 from rfl] at h
  rw [i3387 hinj, i3385 hinj, i3386 hinj, i3388 hinj] at h
  linarith

theorem row1192 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5934 + (1 : ℝ) * HLm Γ 5 L5936 + (-1 : ℝ) * HLm Γ 5 L5938 + (-1 : ℝ) * HLm Γ 5 L5940 := by
  have h := HLm_submod hΓ [F210] L5941 [F90]
  rw [show [F210] ++ L5941 ++ [F90] = L5939 from rfl, show [F210] ++ L5941 = L5935 from rfl,
    show L5941 ++ [F90] = L5937 from rfl] at h
  rw [i3391 hinj, i3389 hinj, i3390 hinj, i3392 hinj] at h
  linarith

theorem row1193 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5942 + (1 : ℝ) * HLm Γ 5 L5944 + (-1 : ℝ) * HLm Γ 5 L5946 + (-1 : ℝ) * HLm Γ 5 L5948 := by
  have h := HLm_submod hΓ [F44] L5949 [F210]
  rw [show [F44] ++ L5949 ++ [F210] = L5947 from rfl, show [F44] ++ L5949 = L5943 from rfl,
    show L5949 ++ [F210] = L5945 from rfl] at h
  rw [i3395 hinj, i3393 hinj, i3394 hinj, i3396 hinj] at h
  linarith

theorem row1194 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5950 + (1 : ℝ) * HLm Γ 5 L4653 + (-1 : ℝ) * HLm Γ 5 L5953 + (-1 : ℝ) * HLm Γ 5 L4649 := by
  have h := HLm_submod hΓ [F2] L5955 [F17]
  rw [show [F2] ++ L5955 ++ [F17] = L5954 from rfl, show [F2] ++ L5955 = L5951 from rfl,
    show L5955 ++ [F17] = L5952 from rfl] at h
  rw [i3399 hinj, i3397 hinj, i3398 hinj, i3400 hinj] at h
  linarith

theorem row1195 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5956 + (1 : ℝ) * HLm Γ 5 L5958 + (-1 : ℝ) * HLm Γ 5 L5960 + (-1 : ℝ) * HLm Γ 5 L4651 := by
  have h := HLm_submod hΓ [F2] L5962 [F228]
  rw [show [F2] ++ L5962 ++ [F228] = L5961 from rfl, show [F2] ++ L5962 = L5957 from rfl,
    show L5962 ++ [F228] = L5959 from rfl] at h
  rw [i3403 hinj, i3401 hinj, i3402 hinj, i3404 hinj] at h
  linarith

theorem row1196 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5963 + (1 : ℝ) * HLm Γ 5 L5965 + (-1 : ℝ) * HLm Γ 5 L5967 + (-1 : ℝ) * HLm Γ 5 L5969 := by
  have h := HLm_submod hΓ [F210] L5970 [F33]
  rw [show [F210] ++ L5970 ++ [F33] = L5968 from rfl, show [F210] ++ L5970 = L5964 from rfl,
    show L5970 ++ [F33] = L5966 from rfl] at h
  rw [i3407 hinj, i3405 hinj, i3406 hinj, i3408 hinj] at h
  linarith

theorem row1197 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5971 + (1 : ℝ) * HLm Γ 5 L5973 + (-1 : ℝ) * HLm Γ 5 L5975 + (-1 : ℝ) * HLm Γ 5 L2376 := by
  have h := HLm_submod hΓ [F210] L5977 [F36]
  rw [show [F210] ++ L5977 ++ [F36] = L5976 from rfl, show [F210] ++ L5977 = L5972 from rfl,
    show L5977 ++ [F36] = L5974 from rfl] at h
  rw [i3411 hinj, i3409 hinj, i3410 hinj, i3412 hinj] at h
  linarith

theorem row1198 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L1451 + (1 : ℝ) * HLm Γ 5 L5067 + (-1 : ℝ) * HLm Γ 5 L4558 + (-1 : ℝ) * HLm Γ 5 L1500 := by
  have h := HLm_submod hΓ [F0] L5981 [F217]
  rw [show [F0] ++ L5981 ++ [F217] = L5980 from rfl, show [F0] ++ L5981 = L5978 from rfl,
    show L5981 ++ [F217] = L5979 from rfl] at h
  rw [i3415 hinj, i3413 hinj, i3414 hinj, i3416 hinj] at h
  linarith

theorem row1199 (Γ : Finset (ℤ × ℤ)) (X Y : Finset ℤ) (hΓ : Γ.Nonempty) (hinj : Inj Γ)
    (hXY : Γ ⊆ X ×ˢ Y) :
    0 ≤ (1 : ℝ) * HLm Γ 5 L5982 + (1 : ℝ) * HLm Γ 5 L5984 + (-1 : ℝ) * HLm Γ 5 L5986 + (-1 : ℝ) * HLm Γ 5 L5988 := by
  have h := HLm_submod hΓ [F7] L5989 [F67]
  rw [show [F7] ++ L5989 ++ [F67] = L5987 from rfl, show [F7] ++ L5989 = L5983 from rfl,
    show L5989 ++ [F67] = L5985 from rfl] at h
  rw [i3419 hinj, i3417 hinj, i3418 hinj, i3420 hinj] at h
  linarith

end EntropyBounds.TwoSet.Certs.R7A5
