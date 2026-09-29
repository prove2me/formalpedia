-- Prove2me | Definitions.Def_Algebra_TropicalLinearAlgebra_MaxPlusSemiring
-- name    : Algebra_TropicalLinearAlgebra_MaxPlusSemiring
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T10:15:49.657102+00:00
-- url     : https://prove2.me/theorems/a28e1a27-5c5b-4a08-b997-d986771b1422
-- title:
--   Aether Catalog definitions — Algebra_TropicalLinearAlgebra_MaxPlusSemiring
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.TropicalLinearAlgebra.MaxPlusSemiring`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/TropicalLinearAlgebra/MaxPlusSemiring.lean by skeleton subtraction
import Mathlib
/-
# The max-plus (tropical) semiring

We construct the tropical semiring `(R ∪ {-∞}, max, +)` as a type synonym
`MaxPlus R := WithBot R` for a linearly ordered additive commutative monoid `R`
(the motivating case being `R = ℝ`), equip it with a `CommSemiring` structure,
and record its characteristic tropical features:

* it is **idempotent**: `a + a = a`;
* it is **zero-sum-free**: `a + b = 0 → a = 0 ∧ b = 0`, so (for nontrivial `R`)
  it admits no additive inverses and is genuinely not a ring;
* finite tropical sums are suprema (`toBot_sum`);
* consequently tropical matrix multiplication is the `max`-of-sums formula and
  is associative.
-/

namespace TropicalLA

/-- Carrier of the max-plus (tropical) semiring: `R ∪ {-∞}`. -/
def MaxPlus (R : Type*) : Type _ := WithBot R

namespace MaxPlus

/-- The identification `R ∪ {-∞} → MaxPlus R`. -/
def ofBot {R : Type*} (x : WithBot R) : MaxPlus R := x

/-- The identification `MaxPlus R → R ∪ {-∞}`. -/
def toBot {R : Type*} (x : MaxPlus R) : WithBot R := x


theorem ofBot_injective {R : Type*} : Function.Injective (ofBot (R := R)) := fun _ _ h => h

instance {R : Type*} : Zero (MaxPlus R) := ⟨ofBot ⊥⟩
instance {R : Type*} [Zero R] : One (MaxPlus R) := ⟨ofBot ((0 : R) : WithBot R)⟩
/-- Tropical addition is `max`. -/
instance {R : Type*} [LinearOrder R] : Add (MaxPlus R) :=
  ⟨fun a b => ofBot (max (toBot a) (toBot b))⟩
/-- Tropical multiplication is ordinary addition. -/
instance {R : Type*} [Add R] : Mul (MaxPlus R) := ⟨fun a b => ofBot (toBot a + toBot b)⟩


variable {R : Type*} [AddCommMonoid R] [LinearOrder R] [IsOrderedAddMonoid R]

instance : CommSemiring (MaxPlus R) where
  add_assoc a b c := congrArg ofBot (max_assoc _ _ _)
  zero_add a := congrArg ofBot (max_eq_right bot_le)
  add_zero a := congrArg ofBot (max_eq_left bot_le)
  add_comm a b := congrArg ofBot (max_comm _ _)
  mul_assoc a b c := congrArg ofBot (add_assoc _ _ _)
  one_mul a := congrArg ofBot (zero_add (toBot a))
  mul_one a := congrArg ofBot (add_zero (toBot a))
  mul_comm a b := congrArg ofBot (add_comm _ _)
  left_distrib a b c := congrArg ofBot (add_max (toBot a) (toBot b) (toBot c))
  right_distrib a b c := congrArg ofBot (max_add (toBot a) (toBot b) (toBot c))
  zero_mul a := congrArg ofBot (WithBot.bot_add (toBot a))
  mul_zero a := congrArg ofBot (WithBot.add_bot (toBot a))
  nsmul := nsmulRec







section Matrices

variable {ι : Type*} [Fintype ι]



end Matrices

end MaxPlus

end TropicalLA


