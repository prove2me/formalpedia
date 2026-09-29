-- Prove2me | Definitions.Def_Novelty_CharacterPolynomialCodes
-- name    : Novelty_CharacterPolynomialCodes
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:08:36.841415+00:00
-- url     : https://prove2.me/theorems/ef821c7b-d70e-4cef-8586-75d439e19da1
-- title:
--   Aether Catalog definitions — Novelty_CharacterPolynomialCodes
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.CharacterPolynomialCodes`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/CharacterPolynomialCodes.lean by skeleton subtraction
import Mathlib

/-!
# Character-polynomial codes: exact image size and nonredundant parameters

This file isolates the algebraic mechanism behind redundancy in a family of
character-polynomial codewords.  A parameter is first sent through a trace-like
additive map and then evaluated coordinatewise.  Equality of codewords is
therefore exactly equality modulo the kernel of that map.  The quotient by the
kernel gives a canonical nonredundant parameter space, and a transversal gives
an equivalent concrete parametrization.
-/

namespace CharacterPolynomialCode

section KernelQuotient

variable {A B W : Type*} [AddCommGroup A] [AddCommGroup B]

/-- A character-polynomial encoder: a trace-like additive map followed by an
injective evaluation/character map. -/
def encoder (trace : A →+ B) (evaluate : B → W) : A → W :=
  fun a => evaluate (trace a)


/-- The encoder descends to the quotient by the trace kernel. -/
def quotientEncoder (trace : A →+ B) (evaluate : B → W) : A ⧸ trace.ker → W :=
  Quotient.lift (encoder trace evaluate) (by
    intro a b hab
    simp only [encoder]
    congr 1
    have hmem : -a + b ∈ trace.ker :=
      (QuotientAddGroup.leftRel_apply).mp hab
    exact neg_add_eq_zero.mp (show -trace a + trace b = 0 by simpa using hmem))



end KernelQuotient

section Transversal

variable {A B W : Type*} [AddCommGroup A] [AddCommGroup B]

/-- A concrete transversal contains exactly one representative of each coset
of the trace kernel. -/
def IsKernelTransversal (trace : A →+ B) (T : Set A) : Prop :=
  ∀ q : A ⧸ trace.ker, ∃! a : A, a ∈ T ∧ (a : A ⧸ trace.ker) = q






end Transversal

section CoordinateFamilies

variable {ι R K W : Type*} [AddCommGroup R] [AddCommGroup K]

/-- The coefficientwise trace on a finite polynomial-support family. -/
def coefficientTrace (trace : K →+ R) : (ι → K) →+ (ι → R) where
  toFun c := fun i => trace (c i)
  map_zero' := by ext i; simp
  map_add' c d := by ext i; simp



end CoordinateFamilies

section LinearCardinality

variable {F K R W : Type*} [Field F] [Fintype F]
  [AddCommGroup K] [Module F K] [Fintype K]
  [AddCommGroup R] [Module F R]


end LinearCardinality

end CharacterPolynomialCode


