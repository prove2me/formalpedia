-- Prove2me | Definitions.Def_ErdosProblems_Erdos68_CanonicalFactorialDigits
-- name    : ErdosProblems_Erdos68_CanonicalFactorialDigits
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-28T01:34:36.377989+00:00
-- url     : https://prove2.me/theorems/f20341d2-7b9a-4d30-a7f5-9e0f7f16c304
-- title:
--   Canonical factorial-scale floor, digit, and remainder
-- statement:
--   For any real x and natural index m, defines the integer floor of m!x, the canonical factorial digit as that floor minus m times the floor at index m−1, and the fractional remainder as m!x minus its floor. The definitions alone assert neither digit bounds nor termination; those are separate theorem nodes.
-- source:
--   Pinned Lean definitions facFloor, canonicalDigit, and canonicalRemainder: https://github.com/wcook04/plectis-erdos-lean/blob/fcb1eff5111efabc25fcf3dfcd6ec48d42ef345c/ErdosProblems/Erdos68/CanonicalFactorialDigits.lean#L26-L36
--   These definitions apply to any real input; the source's rational-tail result is a separate theorem, and this card does not claim irrationality of the Erdős #68 series or novelty of factorial digits.

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

/-- Floor of the `m!`-scaled real number. -/
noncomputable def facFloor (x : ℝ) (m : ℕ) : ℤ :=
  ⌊(m.factorial : ℝ) * x⌋

/-- Canonical radix-`m` factorial digit selected by the floor convention. -/
noncomputable def canonicalDigit (x : ℝ) (m : ℕ) : ℤ :=
  facFloor x m - (m : ℤ) * facFloor x (m - 1)

/-- Fractional remainder after truncation at factorial scale `m!`. -/
noncomputable def canonicalRemainder (x : ℝ) (m : ℕ) : ℝ :=
  (m.factorial : ℝ) * x - (facFloor x m : ℝ)

/-! ## Rational inputs

For a rational number `a / q`, factorial scaling is integral once `q ≤ n`.
Consequently the canonical digit at radix `n + 1` vanishes.  This is a
termination criterion for rational inputs; it does not assert that the Erdős
#68 series is rational or supply recurrence estimates for its partial sums. -/































end ErdosProblems.Erdos68


