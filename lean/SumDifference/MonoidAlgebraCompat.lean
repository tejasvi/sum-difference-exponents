-- Port shim (new file, 2026-10-20), not part of github.com/kleinwaks/sum-difference @ 3664fd11.
import Mathlib.Algebra.MonoidAlgebra.Defs

/-!
# Compatibility shim for `AddMonoidAlgebra`

The original sources (Lean v4.28.0, Mathlib 8f9d9cff) use `AddMonoidAlgebra R G` as a `Finsupp`: `f x` is a
coefficient and `f.support` its support.  In Mathlib c55e6e786f49, `AddMonoidAlgebra R G` is a structure with a
single field `coeff : G →₀ R`.  This file restores the two notations, so that `f x` elaborates to `f.coeff x`
and `f.support` unfolds to `f.coeff.support`; the statements of the ported files keep their meaning.
-/

namespace AddMonoidAlgebra

variable {R G : Type*} [Semiring R]

/-- `f x` is the coefficient `f.coeff x` (as for the former `Finsupp` coercion). -/
instance instCoeFunCoeff : CoeFun (AddMonoidAlgebra R G) (fun _ => G → R) := ⟨fun f => f.coeff⟩

/-- `f.support` is the support of the coefficient function. -/
abbrev support (f : AddMonoidAlgebra R G) : Finset G := f.coeff.support

/-- The former `AddMonoidAlgebra.mul_apply_left`. -/
theorem mul_apply_left [AddGroup G] (x y : AddMonoidAlgebra R G) (g : G) :
    (x * y).coeff g = x.coeff.sum fun h r => r * y.coeff (-h + g) :=
  coeff_mul_apply_left x y g

end AddMonoidAlgebra
