import EntropyBounds.GlueZ.Certs.C3BALL.Final
import EntropyBounds.GlueG.Shuffle

/-!
# `c3b_allgroups.json`: the entropy form without injectivity

`entropy_ineq_general`: `H(X − Y) ≤ λ₁₀ H(X) + λ₀₁ H(Y) + λ₁₁ H(X + Y)` for every finitely supported pair of
random variables in every abelian group `G` (GGSTW Problem 6.30(a), entropy form), from `entropy_ineq` by `entropy_of_injective`;
`entropy_max`: `H(X − Y) ≤ C max(H(X), H(Y), H(X + Y))`, `C = 9213/5036`.
-/

namespace EntropyBounds.GlueZ.Certs.C3BALL

variable {G : Type} [AddCommGroup G] [DecidableEq G]

open EntropyBounds.Iid EntropyBounds.GlueG EntropyBounds.GlueZ SumsDifferences SumsDifferences.NonShannon

theorem entropy_ineq_general (Γ : Finset (G × G)) (p : G × G → ℝ) (hp : ∀ q ∈ Γ, 0 ≤ p q)
    (hs : ∑ q ∈ Γ, p q = 1) :
    pushEntropy Γ p (fun q => q.1 - q.2) ≤ (882 / 1259 : ℝ) * pushEntropy Γ p (fun q => q.1) + (1609 / 2518 : ℝ) * pushEntropy Γ p (fun q => q.2)
      + (2467 / 5036 : ℝ) * pushEntropy Γ p (fun q => q.1 + q.2) :=
  entropy_of_injective (by norm_num) (by norm_num) (by norm_num) (fun Γ p hinj hp hs => entropy_ineq Γ p hinj hp hs)
    Γ p hp hs

theorem entropy_max (Γ : Finset (G × G)) (p : G × G → ℝ) (hp : ∀ q ∈ Γ, 0 ≤ p q) (hs : ∑ q ∈ Γ, p q = 1) :
    pushEntropy Γ p (fun q => q.1 - q.2) ≤ (9213 / 5036 : ℝ) *
      max (max (pushEntropy Γ p (fun q => q.1)) (pushEntropy Γ p (fun q => q.2)))
        (pushEntropy Γ p (fun q => q.1 + q.2)) := by
  have h := entropy_max_of_injective (a := (882 / 1259 : ℝ)) (b := (1609 / 2518 : ℝ)) (c := (2467 / 5036 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (fun Γ p hinj hp hs => entropy_ineq Γ p hinj hp hs) Γ p hp hs
  have e : (882 / 1259 : ℝ) + (1609 / 2518 : ℝ) + (2467 / 5036 : ℝ) = (9213 / 5036 : ℝ) := by norm_num
  rw [e] at h
  exact h

end EntropyBounds.GlueZ.Certs.C3BALL
