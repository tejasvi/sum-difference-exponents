import EntropyBounds.TwoSet.Certs.R7A5.Final
import EntropyBounds.TwoSet.Headline

/-!
# `pair_exponent.json`: the fixed-constant bound without suprema

`admissibleK_le_value`: every exponent `θ` admissible with fixed constants (`AdmissibleK θ`, Tao's page 3a /
GGSTW 6.44) satisfies `θ ≤ 26554427158/20486493787`.  (`thetaK_le` in `Final` is the same bound for the supremum `thetaK`, and
`one_le_thetaK` shows that this supremum is taken over a nonempty bounded set.)
-/

namespace EntropyBounds.TwoSet.Certs.R7A5

open EntropyBounds.TwoSet

theorem admissibleK_le_value {θ : ℝ} (h : AdmissibleK θ) : θ ≤ (26554427158 / 20486493787 : ℝ) := by
  have h1 := admissibleK_le_of_pair_ceiling pair_ceiling h
  norm_num at h1 ⊢
  linarith

end EntropyBounds.TwoSet.Certs.R7A5
