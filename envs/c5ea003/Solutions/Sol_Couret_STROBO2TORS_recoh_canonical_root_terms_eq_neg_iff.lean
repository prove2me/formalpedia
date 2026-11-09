-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_canonical_root_terms_eq_neg_iff
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:41:03.804673+00:00
-- url     : https://prove2.me/submissions/23a17dbc-8d3b-4cda-a51a-a4cf94276e49

import Aesop
import Definitions.Def_Couret_RecohCanonicalCoefficients_7eb0bfadc07d
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
import Mathlib.Data.Finset.Sort
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
import Theorems.Thm_Couret_STROBO2TORS_recoh_canonicalize_terms_eq_iff
import Theorems.Thm_Couret_STROBO2TORS_recoh_canonicalize_terms_negate
import Theorems.Thm_Couret_STROBO2TORS_recoh_normalized_sparse_equal_neg_iff
import Definitions.Def_Couret_RecohCoefficientObservations_4ffca285ab72
import Mathlib.Data.Finset.Sort

set_option autoImplicit false

/-!
Canonical sparse integer coefficient lists.

The Python v0.2 `_terms` routine combines coefficients at equal exponents,
discards zeros, and sorts the remaining exponent/coefficient pairs.  The
definitions below express those operations on already typed lists.  Literal
equality and literal negation of the resulting lists are faithful to the
existing polynomial and complex-value semantics.  JSON parsing and Python
execution are not asserted by this file.
-/

namespace Couret.STROBO2TORS

open Polynomial





































theorem recoh_canonicalize_terms_eq_iff_sparse_equal (xs ys : RecohSparseTerms) :
    recohCanonicalizeTerms xs = recohCanonicalizeTerms ys ↔
      recohSparseEqual xs ys = true := by
  rw [recoh_canonicalize_terms_eq_iff, recoh_sparse_equal_iff]







































theorem p2m_local_recoh_canonical_root_terms_eq_neg_iff {p : ℕ} (hp : p.Prime) (k : ℕ)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (es fs : List ℕ) :
    recohCanonicalRootTerms p k es = recohNegateTerms (recohCanonicalRootTerms p k fs) ↔
      (es.map (ζ ^ ·)).sum = -(fs.map (ζ ^ ·)).sum := by
  rw [recohCanonicalRootTerms, recohCanonicalRootTerms,
    ← recoh_canonicalize_terms_negate, recoh_canonicalize_terms_eq_iff_sparse_equal]
  exact recoh_normalized_sparse_equal_neg_iff hp k hζ es fs



end Couret.STROBO2TORS

theorem solution : ∀ {p : Nat},
  Nat.Prime p →
    ∀ (k : Nat) {ζ : Complex},
      @IsPrimitiveRoot.{0} Complex (@CommRing.toCommMonoid.{0} Complex Complex.commRing) ζ
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid)) p
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
        ∀ (es fs : List.{0} Nat),
          Iff
            (@Eq.{1} Couret.STROBO2TORS.RecohSparseTerms (Couret.STROBO2TORS.recohCanonicalRootTerms p k es)
              (Couret.STROBO2TORS.recohNegateTerms (Couret.STROBO2TORS.recohCanonicalRootTerms p k fs)))
            (@Eq.{1} Complex
              (@List.sum.{0} Complex Complex.instAdd Complex.instZero
                (@List.map.{0, 0} Nat Complex
                  (fun x =>
                    @HPow.hPow.{0, 0, 0} Complex Nat Complex
                      (@instHPow.{0, 0} Complex Nat
                        (@Monoid.toPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)))
                      ζ x)
                  es))
              (@Neg.neg.{0} Complex Complex.instNeg
                (@List.sum.{0} Complex Complex.instAdd Complex.instZero
                  (@List.map.{0, 0} Nat Complex
                    (fun x =>
                      @HPow.hPow.{0, 0, 0} Complex Nat Complex
                        (@instHPow.{0, 0} Complex Nat
                          (@Monoid.toPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)))
                        ζ x)
                    fs)))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_canonical_root_terms_eq_neg_iff

