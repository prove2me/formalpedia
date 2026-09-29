-- Prove2me | Definitions.Def_Tropical_ArithmeticOfSemiringsIdeals
-- name    : Tropical_ArithmeticOfSemiringsIdeals
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:29:19.230067+00:00
-- url     : https://prove2.me/theorems/c65d75e3-92b2-43e7-821f-216aa9bf8e85
-- title:
--   Aether Catalog definitions — Tropical_ArithmeticOfSemiringsIdeals
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.ArithmeticOfSemiringsIdeals`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/ArithmeticOfSemiringsIdeals.lean by skeleton subtraction
import Mathlib

/-!
# The arithmetic of ideals in the natural-number semiring

A formal development of foundational results and a concrete failure of cancellation from
Chen--Hyde--Laurens--Piermarini--Simons, *The Arithmetic of Semirings Part I: Ideals*.
We use Mathlib's existing `Ideal` type for ideals of a semiring.
-/

namespace ArithmeticOfSemirings

/-- Multiplicative similarity: two elements become equal after multiplication by a witness. -/
def Similar {M : Type*} [CommMonoid M] (a b : M) : Prop :=
  ∃ c : M, a * c = b * c






namespace NatIdeal

/-- Similarity with a nonzero ideal witness, as used for ideals of `ℕ`. -/
def Similar (A B : Ideal ℕ) : Prop :=
  ∃ C : Ideal ℕ, C ≠ ⊥ ∧ A * C = B * C

/-- An element is integral over an ideal if multiplication by it preserves some nonzero
ideal witness up to multiplication by the original ideal. -/
def IsIntegralOver (A : Ideal ℕ) (r : ℕ) : Prop :=
  ∃ B : Ideal ℕ, B ≠ ⊥ ∧ Ideal.span {r} * B ≤ A * B

/-- The set-theoretic integral closure. -/
def integralClosure (A : Ideal ℕ) : Set ℕ :=
  {r | IsIntegralOver A r}





section NonCancellation

/-- The first ideal in the paper's explicit noncancellation example. -/
def A : Ideal ℕ := Ideal.span {5, 17}

/-- The strictly larger second ideal in the paper's explicit noncancellation example. -/
def B : Ideal ℕ := Ideal.span ({5, 17, 43} : Set ℕ)

/-- The common factor in the paper's explicit noncancellation example. -/
def C : Ideal ℕ := Ideal.span ({5, 11, 19, 23} : Set ℕ)




end NonCancellation

end NatIdeal
end ArithmeticOfSemirings


