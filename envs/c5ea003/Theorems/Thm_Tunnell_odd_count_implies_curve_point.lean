-- Prove2me | Theorems.Thm_Tunnell_odd_count_implies_curve_point
-- name    : Tunnell.odd_count_implies_curve_point
-- status  : Open
-- author  : @Wenqian Xing
-- created : 2026-09-06T07:25:29.004454+00:00
-- url     : https://prove2.me/theorems/98bd7683-168e-47be-b707-c1a1c61adec6
-- title:
--   Tunnell odd count identity yields a nonzero rational curve point
-- statement:
--   Let \(n\) be a squarefree odd natural number and put
--   \[
--   R_j(n)=\{(x,y,z)\in\mathbb Z^3:n=2x^2+y^2+jz^2\}.
--   \]
--   If \(2|R_{32}(n)|=|R_{8}(n)|\), then there are rational numbers \(x,y\) with
--   \[
--   y\ne0,\qquad y^2=x^3-n^2x.
--   \]
--   This is the unresolved arithmetic existence claim in elliptic-curve coordinates. The proved rational-triangle correspondence converts such a point into the precise congruent-number witness requested by the odd Tunnell mission. No Birch–Swinnerton-Dyer assumption is added: accordingly this statement is left open, just as the mission's unconditional converse is open. It is not asserted to be an unconditional theorem of Tunnell.
-- source:
--   Equivalent elliptic-curve formulation of the odd converse mission, via Keith Conrad, The Congruent Number Problem, Theorem 4.1, pp. 5-6, and Theorem 4.11, p. 12, https://kconrad.math.uconn.edu/blurbs/ugradnumthy/congnumber.pdf. Theorem 4.11 explains the conditional sufficiency under weak BSD. The integer quadratic forms are exactly those of the existing mission, with a swap of the first two coordinates relative to Conrad.

import Mathlib

theorem Tunnell.odd_count_implies_curve_point (n : ℕ) (hsqf : Squarefree n) (hparity : Odd n) :
    2 * ({(x,y,z) : ℤ × ℤ × ℤ | (n : ℤ) = 2 * x ^ 2 + y ^ 2 + 32 * z ^ 2} : Set (ℤ × ℤ × ℤ)).ncard =
      ({(x,y,z) : ℤ × ℤ × ℤ | (n : ℤ) = 2 * x ^ 2 + y ^ 2 + 8 * z ^ 2} : Set (ℤ × ℤ × ℤ)).ncard →
    ∃ x y : ℚ, y ≠ 0 ∧ y ^ 2 = x ^ 3 - (n : ℚ) ^ 2 * x := by sorry
