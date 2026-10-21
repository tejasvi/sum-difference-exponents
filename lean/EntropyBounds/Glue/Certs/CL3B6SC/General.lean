import EntropyBounds.Glue.Certs.CL3B6SC.Final
import EntropyBounds.Glue.Shuffle

/-!
# `c3b_torsionfree.json`: the entropy form without injectivity

`entropy_ineq_general`: `H(X − Y) ≤ λ₁₀ H(X) + λ₀₁ H(Y) + λ₁₁ H(X + Y)` for every finitely supported pair of real
random variables (GGSTW Problem 6.30(a), entropy form), from `entropy_ineq` by `entropy_of_injective`;
`entropy_max`: `H(X − Y) ≤ C max(H(X), H(Y), H(X + Y))`, `C = 4785864240814563464816432634036471899/2619096017836492522862695316182077572`.
-/

namespace EntropyBounds.Glue.Certs.CL3B6SC

open EntropyBounds.Iid EntropyBounds.Glue SumsDifferences SumsDifferences.NonShannon

theorem entropy_ineq_general (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (hp : ∀ q ∈ Γ, 0 ≤ p q)
    (hs : ∑ q ∈ Γ, p q = 1) :
    pushEntropy Γ p (fun q => q.1 - q.2) ≤ (925252334339885103560423126733856553 / 1309548008918246261431347658091038786 : ℝ) * pushEntropy Γ p (fun q => q.1) + (424585766727935297449756583005066048 / 654774004459123130715673829045519393 : ℝ) * pushEntropy Γ p (fun q => q.2)
      + (1237016505223052067896560048548494601 / 2619096017836492522862695316182077572 : ℝ) * pushEntropy Γ p (fun q => q.1 + q.2) :=
  entropy_of_injective (by norm_num) (by norm_num) (by norm_num) (fun Γ p hinj hp hs => entropy_ineq Γ p hinj hp hs)
    Γ p hp hs

theorem entropy_max (Γ : Finset (ℝ × ℝ)) (p : ℝ × ℝ → ℝ) (hp : ∀ q ∈ Γ, 0 ≤ p q) (hs : ∑ q ∈ Γ, p q = 1) :
    pushEntropy Γ p (fun q => q.1 - q.2) ≤ (4785864240814563464816432634036471899 / 2619096017836492522862695316182077572 : ℝ) *
      max (max (pushEntropy Γ p (fun q => q.1)) (pushEntropy Γ p (fun q => q.2)))
        (pushEntropy Γ p (fun q => q.1 + q.2)) := by
  have h := entropy_max_of_injective (a := (925252334339885103560423126733856553 / 1309548008918246261431347658091038786 : ℝ)) (b := (424585766727935297449756583005066048 / 654774004459123130715673829045519393 : ℝ)) (c := (1237016505223052067896560048548494601 / 2619096017836492522862695316182077572 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (fun Γ p hinj hp hs => entropy_ineq Γ p hinj hp hs) Γ p hp hs
  have e : (925252334339885103560423126733856553 / 1309548008918246261431347658091038786 : ℝ) + (424585766727935297449756583005066048 / 654774004459123130715673829045519393 : ℝ) + (1237016505223052067896560048548494601 / 2619096017836492522862695316182077572 : ℝ) = (4785864240814563464816432634036471899 / 2619096017836492522862695316182077572 : ℝ) := by norm_num
  rw [e] at h
  exact h

end EntropyBounds.Glue.Certs.CL3B6SC
