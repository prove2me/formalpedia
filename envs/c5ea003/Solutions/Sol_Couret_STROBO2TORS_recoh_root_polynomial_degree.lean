-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_root_polynomial_degree
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:01:53.600296+00:00
-- url     : https://prove2.me/submissions/58a5c139-1ef5-4f24-a765-d04770d7dd00

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

















theorem p2m_local_recoh_root_polynomial_degree {p : ℕ} (hp : p.Prime) (k e : ℕ) :
    (recohRootPolynomial p k e).degree < ((p - 1) * p ^ k : ℕ) := by
  unfold recohRootPolynomial
  dsimp only
  split_ifs with h
  · rw [degree_X_pow]
    exact WithBot.coe_lt_coe.mpr h
  · rw [degree_neg]
    apply lt_of_le_of_lt (degree_sum_le _ _)
    apply (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr
    intro j hj
    rw [degree_X_pow]
    apply WithBot.coe_lt_coe.mpr
    have ht := Nat.mod_lt (e % p ^ (k + 1)) (pow_pos hp.pos k)
    calc
      j * p ^ k + e % p ^ (k + 1) % p ^ k < j * p ^ k + p ^ k :=
        Nat.add_lt_add_left ht _
      _ = (j + 1) * p ^ k := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ (p - 1) * p ^ k :=
        Nat.mul_le_mul_right _ (Nat.succ_le_of_lt (Finset.mem_range.mp hj))









/-! ## Executable sparse terms and their polynomial interpretation -/

























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
    ∀ (k e : Nat),
      @LT.lt.{0} (WithBot.{0} Nat)
        (@Preorder.toLT.{0} (WithBot.{0} Nat) (@WithBot.instPreorder.{0} Nat Nat.instPreorder))
        (@Polynomial.degree.{0} Int Int.instSemiring (Couret.STROBO2TORS.recohRootPolynomial p k e))
        (@Nat.cast.{0} (WithBot.{0} Nat) (@WithBot.natCast.{0} Nat instNatCastNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) p
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid)) p k))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_root_polynomial_degree

