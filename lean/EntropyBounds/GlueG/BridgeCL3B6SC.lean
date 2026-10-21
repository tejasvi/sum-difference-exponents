import EntropyBounds.GlueG.Certs.CL3B6SC.General
import EntropyBounds.GlueG.SetFormProd
import EntropyBounds.Glue.Certs.CL3B6SC.General
import EntropyBounds.Glue.Certs.CL3B6SC.Product

/-!
# `c3b_torsionfree.json` in abelian groups without 2-torsion: product form, torsion-free case, bridge to `ℝ`

`EntropyBounds.GlueG.Certs.CL3B6SC` proves the certificate's inequalities for every abelian group `G : Type` in which
doubling is injective (`h2 : ∀ x : G, x + x = 0 → x = 0`): `entropy_ineq` (injective pairs), `entropy_ineq_general`
and `entropy_max` (all finitely supported pairs), `set_ineq'` (max form of the set inequality).  Here:

* `set_ineq_prod`: the product form `|A −_P B| ≤ |A|^λ_X |B|^λ_Y |A +_P B|^λ_S` (Theorem 1.1(b) of the paper);
* `entropy_ineq_general_torsionFree`, `set_ineq'_torsionFree`, `set_ineq_prod_torsionFree`: torsion-free groups;
* `bridge_entropy_ineq`, `bridge_entropy_ineq_general`, `bridge_set_ineq'`, `bridge_set_ineq_prod`: at `G = ℝ` the
  group theorems prove the statements of `EntropyBounds.Glue.Certs.CL3B6SC` verbatim (`type_of%` of the real
  theorems); in particular the numbers `λ` below are those of the real certificate files.
-/

open Finset

namespace EntropyBounds.GlueG.Certs.CL3B6SC

open SumsDifferences

/-- Doubling is injective on `ℝ`. -/
theorem real_two : ∀ x : ℝ, x + x = 0 → x = 0 := fun x hx => by linarith

/-- Doubling is injective on a torsion-free abelian group. -/
theorem two_of_torsionFree {G : Type} [AddCommGroup G] [IsAddTorsionFree G] : ∀ x : G, x + x = 0 → x = 0 := by
  intro x hx
  have h2 : (2 : ℕ) • x = (2 : ℕ) • (0 : G) := by rw [two_nsmul, hx, smul_zero]
  exact nsmul_right_injective (by norm_num : (2 : ℕ) ≠ 0) h2

/-- **The product form of the set inequality** in an abelian group without 2-torsion. -/
theorem set_ineq_prod {G : Type} [AddCommGroup G] [DecidableEq G] (h2 : ∀ x : G, x + x = 0 → x = 0)
    (A B : Finset G) (P : Finset (G × G)) (hP : P ⊆ A ×ˢ B) :
    (#(P.image fun q => q.1 - q.2) : ℝ)
      ≤ (#A : ℝ) ^ (925252334339885103560423126733856553 / 1309548008918246261431347658091038786 : ℝ)
        * (#B : ℝ) ^ (424585766727935297449756583005066048 / 654774004459123130715673829045519393 : ℝ)
        * (#(P.image fun q => q.1 + q.2) : ℝ) ^ (1237016505223052067896560048548494601 / 2619096017836492522862695316182077572 : ℝ) :=
  set_form_prod (by norm_num) (by norm_num) (by norm_num) (fun Γ p hinj hp hs => entropy_ineq Γ p h2 hinj hp hs)
    A B P hP

/-- The entropy form without injectivity in a torsion-free abelian group. -/
theorem entropy_ineq_general_torsionFree {G : Type} [AddCommGroup G] [IsAddTorsionFree G] [DecidableEq G] :
    type_of% (entropy_ineq_general (G := G) two_of_torsionFree) :=
  entropy_ineq_general (G := G) two_of_torsionFree

/-- The max form of the set inequality in a torsion-free abelian group. -/
theorem set_ineq'_torsionFree {G : Type} [AddCommGroup G] [IsAddTorsionFree G] [DecidableEq G] :
    type_of% (set_ineq' (G := G) two_of_torsionFree) :=
  set_ineq' (G := G) two_of_torsionFree

/-- The product form of the set inequality in a torsion-free abelian group. -/
theorem set_ineq_prod_torsionFree {G : Type} [AddCommGroup G] [IsAddTorsionFree G] [DecidableEq G] :
    type_of% (set_ineq_prod (G := G) two_of_torsionFree) :=
  set_ineq_prod (G := G) two_of_torsionFree

/-- At `G = ℝ`: the statement of `EntropyBounds.Glue.Certs.CL3B6SC.entropy_ineq`. -/
theorem bridge_entropy_ineq : type_of% @EntropyBounds.Glue.Certs.CL3B6SC.entropy_ineq :=
  fun Γ p hinj hp hs => entropy_ineq (G := ℝ) Γ p real_two hinj hp hs

/-- At `G = ℝ`: the statement of `EntropyBounds.Glue.Certs.CL3B6SC.entropy_ineq_general`. -/
theorem bridge_entropy_ineq_general : type_of% @EntropyBounds.Glue.Certs.CL3B6SC.entropy_ineq_general :=
  entropy_ineq_general (G := ℝ) real_two

/-- At `G = ℝ`: the statement of `EntropyBounds.Glue.Certs.CL3B6SC.set_ineq'` (Tao's page 3b set form). -/
theorem bridge_set_ineq' : type_of% @EntropyBounds.Glue.Certs.CL3B6SC.set_ineq' :=
  set_ineq' (G := ℝ) real_two

/-- At `G = ℝ`: the statement of `EntropyBounds.Glue.Certs.CL3B6SC.set_ineq_prod`. -/
theorem bridge_set_ineq_prod : type_of% @EntropyBounds.Glue.Certs.CL3B6SC.set_ineq_prod :=
  set_ineq_prod (G := ℝ) real_two

end EntropyBounds.GlueG.Certs.CL3B6SC
