-- Prove2me | solution 1 for ErdosProblems.Erdos68.canonicalDigit_eq_floor_mul_remainder
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-28T01:36:05.714986+00:00
-- url     : https://prove2.me/submissions/738d6b99-e94c-4990-8963-572761982aa8

import Definitions.Def_ErdosProblems_Erdos68_CanonicalFactorialDigits
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

/-!
# Erdős #68: canonical factorial digits

For the factorial-denominator series

`sum (n >= 2), 1 / (n! - 1)`.

the natural factorial-scale floors give a mixed-radix digit expansion.  This
module develops that expansion for an arbitrary real number: the digits lie
in their canonical ranges, the fractional remainders satisfy the radix
recurrence, and every finite truncation has an explicit remainder term.

The construction is independent of the particular series.  Applied to
Erdős #68, it reduces the digit approach to proving that the canonical
remainder never enters a terminal zero tail.
-/

namespace ErdosProblems.Erdos68
open scoped BigOperators







/-! ## Rational inputs

For a rational number `a / q`, factorial scaling is integral once `q ≤ n`.
Consequently the canonical digit at radix `n + 1` vanishes.  This is a
termination criterion for rational inputs; it does not assert that the Erdős
#68 series is rational or supply recurrence estimates for its partial sums. -/





private theorem factorial_eq_mul_pred_factorial (m : ℕ) (hm : 1 ≤ m) :
    m.factorial = m * (m - 1).factorial := by
  have hmsucc : m - 1 + 1 = m := by omega
  calc
    m.factorial = (m - 1 + 1).factorial := by rw [hmsucc]
    _ = (m - 1 + 1) * (m - 1).factorial := Nat.factorial_succ _
    _ = m * (m - 1).factorial := by rw [hmsucc]
end ErdosProblems.Erdos68

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos68 in
theorem solution
    (x : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    canonicalDigit x m =
      ⌊(m : ℝ) * canonicalRemainder x (m - 1)⌋ := by
  have hfacNat := factorial_eq_mul_pred_factorial m hm
  have hfac :
      (m.factorial : ℝ) =
        (m : ℝ) * ((m - 1).factorial : ℝ) := by
    exact_mod_cast hfacNat
  unfold canonicalDigit canonicalRemainder facFloor
  rw [hfac]
  have hrewrite :
      (m : ℝ) *
          (((m - 1).factorial : ℝ) * x -
            (⌊((m - 1).factorial : ℝ) * x⌋ : ℝ)) =
        (m : ℝ) * ((m - 1).factorial : ℝ) * x -
          (((m : ℤ) * ⌊((m - 1).factorial : ℝ) * x⌋ : ℤ) : ℝ) := by
    push_cast
    ring
  rw [hrewrite, Int.floor_sub_intCast]
