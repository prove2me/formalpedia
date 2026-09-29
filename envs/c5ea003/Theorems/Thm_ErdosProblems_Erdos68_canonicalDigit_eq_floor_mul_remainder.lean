-- Prove2me | Theorems.Thm_ErdosProblems_Erdos68_canonicalDigit_eq_floor_mul_remainder
-- name    : ErdosProblems.Erdos68.canonicalDigit_eq_floor_mul_remainder
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-28T01:35:09.793981+00:00
-- url     : https://prove2.me/theorems/a3ce8340-db1b-4e22-825b-e82d57e32b5b
-- title:
--   A canonical factorial digit is the floor of the scaled preceding remainder
-- statement:
--   For every real x and natural m ≥ 1, the canonical factorial digit at m equals the integer floor of m times the canonical remainder at m−1.
-- source:
--   Pinned Lean theorem and proof: https://github.com/wcook04/plectis-erdos-lean/blob/fcb1eff5111efabc25fcf3dfcd6ec48d42ef345c/ErdosProblems/Erdos68/CanonicalFactorialDigits.lean#L124-L143
--   This identity applies to arbitrary real x and does not prove anything about the irrationality of the specific Erdős #68 series.

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


open scoped BigOperators







/-! ## Rational inputs

For a rational number `a / q`, factorial scaling is integral once `q ≤ n`.
Consequently the canonical digit at radix `n + 1` vanishes.  This is a
termination criterion for rational inputs; it does not assert that the Erdős
#68 series is rational or supply recurrence estimates for its partial sums. -/

open ErdosProblems.Erdos68

theorem ErdosProblems.Erdos68.canonicalDigit_eq_floor_mul_remainder
    (x : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    canonicalDigit x m =
      ⌊(m : ℝ) * canonicalRemainder x (m - 1)⌋ := by sorry
