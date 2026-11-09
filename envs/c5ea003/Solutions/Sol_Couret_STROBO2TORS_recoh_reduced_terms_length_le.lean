-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_reduced_terms_length_le
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:42:29.407404+00:00
-- url     : https://prove2.me/submissions/1994ea0d-d91b-4534-8b89-250599229cdd

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

















theorem recoh_root_terms_length_le {p : ℕ} (hp : p.Prime) (k e : ℕ) :
    (recohRootTerms p k e).length ≤ p - 1 := by
  unfold recohRootTerms
  dsimp only
  split_ifs
  · simp only [List.length_cons, List.length_nil]
    have := hp.two_le
    omega
  · simp only [List.length_map, List.length_range, le_refl]

theorem p2m_local_recoh_reduced_terms_length_le {p : ℕ} (hp : p.Prime) (k : ℕ) (es : List ℕ) :
    (recohReducedTerms p k es).length ≤ es.length * (p - 1) := by
  induction es with
  | nil => simp [recohReducedTerms]
  | cons e es ih =>
    simp only [recohReducedTerms, List.flatMap_cons, List.length_append]
    calc
      _ ≤ (p - 1) + es.length * (p - 1) :=
        Nat.add_le_add (recoh_root_terms_length_le hp k e) ih
      _ = (e :: es).length * (p - 1) := by
        simp only [List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm]





/-! ## Executable equality by summing coefficients at present exponents -/























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
    ∀ (k : Nat) (es : List.{0} Nat),
      @LE.le.{0} Nat instLENat (@List.length.{0} (Prod.{0, 0} Nat Int) (Couret.STROBO2TORS.recohReducedTerms p k es))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@List.length.{0} Nat es)
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) p
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_reduced_terms_length_le

