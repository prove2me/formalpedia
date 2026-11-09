-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_coefficient_match_neg_iff
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:02:25.395674+00:00
-- url     : https://prove2.me/submissions/8b4b6adc-9cb6-406e-bcf4-41cb2df50d40

import Aesop
import Definitions.Def_Couret_RecohCoefficientObservations_4ffca285ab72
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_coefficient_value_negate
import Theorems.Thm_Couret_STROBO2TORS_recoh_coefficients_reduced_negate
import Definitions.Def_Couret_RecohSparseObservation_6dd9be0e8eb2

set_option autoImplicit false

/-!
Exact observation checking from integer cyclotomic coefficients.

Observed readings are supplied directly as lists of pairs `(exponent,
integer coefficient)`.  No conversion from coefficients back to root lists
is used.  Complex values occur only in the interpretation and correctness
theorems; all checkers compare natural numbers and integer coefficients.

The range contract is sufficient for faithful evaluation.  The stronger
typed-format contract also excludes zero coefficients and repeated
exponents, matching the conditions inspected by Python `_read_coefficients`.
It does not certify JSON parsing, Python execution or sorting.
-/

namespace Couret.STROBO2TORS

open Polynomial
open scoped BigOperators



































theorem p2m_local_recoh_coefficient_match_neg_iff {p : ℕ} (hp : p.Prime) (k : ℕ)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (p ^ (k + 1)))
    (es : List ℕ) (terms : RecohSparseTerms) (ht : RecohCoefficientsReduced p k terms) :
    recohCoefficientMatchNeg p k es terms = true ↔
      -(es.map (ζ ^ ·)).sum = recohCoefficientValue ζ terms := by
  rw [recohCoefficientMatchNeg, recoh_reduced_coefficients_equal_iff hp k hζ _ _
    (recoh_coefficients_reduced_negate p k _ (recoh_reduced_terms_reduced hp k es)) ht,
    recoh_coefficient_value_negate, recoh_reduced_terms_value hp k hζ es]

variable {G : Type*} [AddCommGroup G] [DecidableEq G]













/-!
The coefficient checkers do not themselves establish support coverage,
primality, primitive-root identities or the interpretation of candidate
encodings.  Their correctness theorems display these contracts explicitly.
The observed coefficient values require no witness as a sum of three roots.
Such a representation, if it exists, is supplied by a successfully checked
candidate rather than assumed as an input encoding.

Typed lists may be arbitrarily long.  No constant or bit-complexity bound
for reading or checking observed input is asserted here.  In particular,
the twelve-position bound for comparing two normalized triples is not a
bound on arbitrary externally supplied coefficient lists.
-/


end Couret.STROBO2TORS

theorem solution : ∀ {p : Nat},
  Nat.Prime p →
    ∀ (k : Nat) {ζ : Complex},
      @IsPrimitiveRoot.{0} Complex (@CommRing.toCommMonoid.{0} Complex Complex.commRing) ζ
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid)) p
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
        ∀ (es : List.{0} Nat) (terms : Couret.STROBO2TORS.RecohSparseTerms),
          Couret.STROBO2TORS.RecohCoefficientsReduced p k terms →
            Iff (@Eq.{1} Bool (Couret.STROBO2TORS.recohCoefficientMatchNeg p k es terms) Bool.true)
              (@Eq.{1} Complex
                (@Neg.neg.{0} Complex Complex.instNeg
                  (@List.sum.{0} Complex Complex.instAdd Complex.instZero
                    (@List.map.{0, 0} Nat Complex
                      (fun x =>
                        @HPow.hPow.{0, 0, 0} Complex Nat Complex
                          (@instHPow.{0, 0} Complex Nat
                            (@Monoid.toPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)))
                          ζ x)
                      es)))
                (Couret.STROBO2TORS.recohCoefficientValue ζ terms)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_coefficient_match_neg_iff

