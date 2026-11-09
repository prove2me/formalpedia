-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_normalized_sparse_equal_iff
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:17:02.884758+00:00
-- url     : https://prove2.me/submissions/783f5a05-a1ff-4cac-a5da-13fb79bbc8fe

import Definitions.Def_Couret_RecohCyclotomicNormalization_6797485e207c
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic
import Theorems.Thm_Couret_STROBO2TORS_recoh_root_polynomial_degree
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























theorem recoh_root_sum_polynomial_degree {p : ℕ} (hp : p.Prime) (k : ℕ)
    (es : List ℕ) :
    (recohRootSumPolynomial p k es).degree < ((p - 1) * p ^ k : ℕ) := by
  induction es with
  | nil =>
    simpa only [recohRootSumPolynomial, List.map_nil, List.sum_nil, degree_zero]
      using (WithBot.bot_lt_coe ((p - 1) * p ^ k))
  | cons e es ih =>
    simp only [recohRootSumPolynomial, List.map_cons, List.sum_cons]
    exact lt_of_le_of_lt (degree_add_le _ _)
      (max_lt (recoh_root_polynomial_degree hp k e) ih)

/-- Equality of reduced polynomial forms is equivalent to exact complex
equality.  It is not an injectivity statement about raw lists of terms. -/
theorem recoh_root_sum_polynomial_eq_iff {p : ℕ} (hp : p.Prime) (k : ℕ)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (es fs : List ℕ) :
    recohRootSumPolynomial p k es = recohRootSumPolynomial p k fs ↔
      (es.map (ζ ^ ·)).sum = (fs.map (ζ ^ ·)).sum := by
  have degree_bound (xs : List ℕ) :
      (recohRootSumPolynomial p k xs).degree < ((p ^ (k + 1)).totient : WithBot ℕ) := by
    simpa only [Nat.totient_prime_pow_succ hp, Nat.mul_comm] using
      recoh_root_sum_polynomial_degree hp k xs
  rw [← recoh_root_sum_polynomial_aeval hp k hζ es,
    ← recoh_root_sum_polynomial_aeval hp k hζ fs]
  exact (recoh_cyclotomic_eval_eq_iff (pow_pos hp.pos _) hζ _ _
    (degree_bound es) (degree_bound fs)).symm

/-! ## Executable sparse terms and their polynomial interpretation -/

























/-! ## Executable equality by summing coefficients at present exponents -/











/-- The executable sparse test decides equality of the original complex
root sums exactly.  Its proof applies to every prime, including 2 and 3. -/
theorem p2m_local_recoh_normalized_sparse_equal_iff {p : ℕ} (hp : p.Prime) (k : ℕ)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (es fs : List ℕ) :
    recohSparseEqual (recohReducedTerms p k es) (recohReducedTerms p k fs) = true ↔
      (es.map (ζ ^ ·)).sum = (fs.map (ζ ^ ·)).sum := by
  rw [recoh_sparse_equal_iff, recoh_reduced_terms_polynomial,
    recoh_reduced_terms_polynomial]
  exact recoh_root_sum_polynomial_eq_iff hp k hζ es fs











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

theorem solution : ∀ {p : Nat},
  Nat.Prime p →
    ∀ (k : Nat) {ζ : Complex},
      @IsPrimitiveRoot.{0} Complex (@CommRing.toCommMonoid.{0} Complex Complex.commRing) ζ
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid)) p
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
        ∀ (es fs : List.{0} Nat),
          Iff
            (@Eq.{1} Bool
              (Couret.STROBO2TORS.recohSparseEqual (Couret.STROBO2TORS.recohReducedTerms p k es)
                (Couret.STROBO2TORS.recohReducedTerms p k fs))
              Bool.true)
            (@Eq.{1} Complex
              (@List.sum.{0} Complex Complex.instAdd Complex.instZero
                (@List.map.{0, 0} Nat Complex
                  (fun x =>
                    @HPow.hPow.{0, 0, 0} Complex Nat Complex
                      (@instHPow.{0, 0} Complex Nat
                        (@Monoid.toPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)))
                      ζ x)
                  es))
              (@List.sum.{0} Complex Complex.instAdd Complex.instZero
                (@List.map.{0, 0} Nat Complex
                  (fun x =>
                    @HPow.hPow.{0, 0, 0} Complex Nat Complex
                      (@instHPow.{0, 0} Complex Nat
                        (@Monoid.toPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)))
                      ζ x)
                  fs))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_normalized_sparse_equal_iff

