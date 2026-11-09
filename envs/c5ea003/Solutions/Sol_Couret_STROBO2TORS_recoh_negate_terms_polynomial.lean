-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_negate_terms_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:49:22.031069+00:00
-- url     : https://prove2.me/submissions/87d69a1a-7f01-4d3c-b04c-d0989e2e2443

import Definitions.Def_Couret_RecohCyclotomicNormalization_6797485e207c
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic

set_option autoImplicit false

/-!
Exact integer-polynomial normalization for primary character sums.

The parameter `k` is one less than the positive primary exponent: the order
is `p ^ (k + 1)` and the stride is `p ^ k`.  Executable reduction uses lists
of integer monomials.  Mathlib's noncomputable integer-polynomial operations
provide their semantics; complex evaluation occurs in correctness theorems.
The separate Python `cyclotomic_sum` implementation is not extracted from,
or certified by, this module.
-/

namespace Couret.STROBO2TORS

open Polynomial
open scoped BigOperators



























/-! ## Executable sparse terms and their polynomial interpretation -/

























/-! ## Executable equality by summing coefficients at present exponents -/



















theorem p2m_local_recoh_negate_terms_polynomial (ts : RecohSparseTerms) :
    recohTermsPolynomial (recohNegateTerms ts) = -recohTermsPolynomial ts := by
  induction ts with
  | nil => simp [recohNegateTerms, recohTermsPolynomial]
  | cons t ts ih =>
    simp only [recohNegateTerms, List.map_cons, recohTermsPolynomial, monomial_neg]
    rw [show recohTermsPolynomial (ts.map (fun t => (t.1, -t.2))) =
        -recohTermsPolynomial ts from ih]
    exact (neg_add _ _).symm



/-!
## Boundary with the separate Python implementation

`recohRootTerms` uses the same exponent reduction and the same emitted
integer monomials as `cyclotomic_sum` in `../recoh_exact_decoder.py`, with
`order = p ^ (k + 1)` and `stride = p ^ k`.  The Python code subsequently
combines coefficients with `Counter`, omits zeros and sorts by exponent.

The theorems in this module certify the Lean term-list reduction and its
coefficient-summing comparator.  They identify exact equality with equality
of the interpreted integer polynomials and then with complex equality.
They do not certify Python execution, its container operations, parsing,
the extraction of primary orders, or a canonical sorted-list representation.
There is no theorem asserting injectivity of raw monomial lists.

For two normalized triples with prime 2 or 3, the comparator visits at most
twelve exponent positions.  Each test scans both finite term lists.  The
length bounds above do not constitute a bit-complexity theorem: exponent
reduction, integer arithmetic and input reading retain their own costs.
-/


end Couret.STROBO2TORS

theorem solution : ∀ (ts : Couret.STROBO2TORS.RecohSparseTerms),
  @Eq.{1} (@Polynomial.{0} Int Int.instSemiring)
    (Couret.STROBO2TORS.recohTermsPolynomial (Couret.STROBO2TORS.recohNegateTerms ts))
    (@Neg.neg.{0} (@Polynomial.{0} Int Int.instSemiring) (@Polynomial.instNeg.{0} Int Int.instRing)
      (Couret.STROBO2TORS.recohTermsPolynomial ts)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_negate_terms_polynomial

