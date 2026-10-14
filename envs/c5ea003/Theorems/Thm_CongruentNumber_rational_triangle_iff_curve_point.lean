-- Prove2me | Theorems.Thm_CongruentNumber_rational_triangle_iff_curve_point
-- name    : CongruentNumber.rational_triangle_iff_curve_point
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-09-06T07:23:26.619257+00:00
-- url     : https://prove2.me/theorems/d16cf0fb-2793-443f-89bf-c7f80e9b70ce
-- title:
--   Rational right triangles and nonzero points on the congruent-number curve
-- statement:
--   For a positive rational n, a rational Pythagorean triple of signed side lengths with signed area n exists if and only if the curve y squared = x cubed minus n squared times x has a rational point with nonzero y coordinate. The signed-side convention is the one used by congruentNumberDM in both Tunnell missions; since n is positive it also yields an ordinary positive-sided rational right triangle by taking absolute values. This theorem proves the elementary algebraic correspondence only; it makes no assertion about when either type of solution exists.
-- source:
--   Keith Conrad, The Congruent Number Problem, Theorem 4.1 and the following discussion, pp. 5-6, https://kconrad.math.uconn.edu/blurbs/ugradnumthy/congnumber.pdf. The submitted proof uses the algebraically equivalent forward coordinates x=a(a+c)/2 and y=a squared times (a+c)/2.

import Mathlib.Data.Rat.Cast.Order

set_option autoImplicit false

theorem CongruentNumber.rational_triangle_iff_curve_point (n : ℚ) (hn : 0 < n) :
    (∃ a b c : ℚ, a ^ 2 + b ^ 2 = c ^ 2 ∧ n = (2⁻¹ : ℚ) * a * b) ↔
      ∃ x y : ℚ, y ≠ 0 ∧ y ^ 2 = x ^ 3 - n ^ 2 * x := by sorry
