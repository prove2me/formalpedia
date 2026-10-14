-- Prove2me | Theorems.Thm_Tunnell_even_count_implies_curve_point
-- name    : Tunnell.even_count_implies_curve_point
-- status  : Open
-- author  : @Wenqian Xing
-- created : 2026-09-06T07:25:36.834156+00:00
-- url     : https://prove2.me/theorems/09241fa6-0cbc-4182-85a2-945bc0dc0722
-- title:
--   Tunnell even count identity yields a nonzero rational curve point
-- statement:
--   Let \(n\) be a squarefree even natural number and put
--   \[
--   R_j(n)=\{(x,y,z)\in\mathbb Z^3:n=8x^2+2y^2+jz^2\}.
--   \]
--   If \(2|R_{64}(n)|=|R_{16}(n)|\), then there are rational numbers \(x,y\) with
--   \[
--   y\ne0,\qquad y^2=x^3-n^2x.
--   \]
--   This is the unresolved arithmetic existence claim in elliptic-curve coordinates. The proved rational-triangle correspondence converts such a point into the precise congruent-number witness requested by the even Tunnell mission. No Birch–Swinnerton-Dyer assumption is added: accordingly this statement is left open, just as the mission's unconditional converse is open. It is not asserted to be an unconditional theorem of Tunnell.
-- source:
--   Equivalent elliptic-curve formulation of the even converse mission, via Keith Conrad, The Congruent Number Problem, Theorem 4.1, pp. 5-6, and Theorem 4.11, p. 12, https://kconrad.math.uconn.edu/blurbs/ugradnumthy/congnumber.pdf. Theorem 4.11 explains the conditional sufficiency under weak BSD. The integer quadratic forms are exactly those of the existing mission, with a swap of the first two coordinates relative to Conrad.

import Mathlib

theorem Tunnell.even_count_implies_curve_point (n : ℕ) (hsqf : Squarefree n) (hparity : Even n) :
    2 * ({(x,y,z) : ℤ × ℤ × ℤ | (n : ℤ) = 8 * x ^ 2 + 2 * y ^ 2 + 64 * z ^ 2} : Set (ℤ × ℤ × ℤ)).ncard =
      ({(x,y,z) : ℤ × ℤ × ℤ | (n : ℤ) = 8 * x ^ 2 + 2 * y ^ 2 + 16 * z ^ 2} : Set (ℤ × ℤ × ℤ)).ncard →
    ∃ x y : ℚ, y ≠ 0 ∧ y ^ 2 = x ^ 3 - (n : ℚ) ^ 2 * x := by sorry
