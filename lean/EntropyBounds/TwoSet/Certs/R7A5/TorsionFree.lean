import EntropyBounds.TwoSet.Certs.R7A5.Final
import EntropyBounds.TwoSet.TorsionFree

/-!
# `pair_exponent.json` in torsion-free abelian groups

`pair_ceiling_torsionFree`: `|X − Y| ≤ |X + Y|^λ` for all finite subsets `X, Y` of a torsion-free abelian group,
`λ = 20486493787/14418560416`, from `pair_ceiling` (finite subsets of `ℤ`) by `card_sub_le_of_int`.
-/

open Finset Pointwise

namespace EntropyBounds.TwoSet.Certs.R7A5

open EntropyBounds.TwoSet

theorem pair_ceiling_torsionFree {G : Type*} [AddCommGroup G] [IsAddTorsionFree G] [DecidableEq G]
    (X Y : Finset G) : (#(X - Y) : ℝ) ≤ (#(X + Y) : ℝ) ^ (20486493787 / 14418560416 : ℝ) :=
  card_sub_le_of_int pair_ceiling X Y

end EntropyBounds.TwoSet.Certs.R7A5
