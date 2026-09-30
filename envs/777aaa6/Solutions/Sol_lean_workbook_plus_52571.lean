-- Prove2me | solution 1 for lean_workbook_plus_52571
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:40:59.361298+00:00
-- url     : https://prove2.me/submissions/acceafe2-ced3-4899-8227-5f789110b50a

import Mathlib.Analysis.Complex.Basic

theorem solution (x y z P: ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hP: P = x + y + z) (h : 2*x + 4*y + 7*z = 2*x*y*z) : P >= 3 := by
  subst hP
  have hs : 0 < x + y + z := by linarith
  -- AM-GM: 27xyz ≤ (x+y+z)^3
  have amgm : 27 * (x * y * z) ≤ (x + y + z)^3 := by
    nlinarith [mul_nonneg (add_nonneg (add_nonneg hx.le hy.le) hz.le) (sq_nonneg (x - y)),
      mul_nonneg (add_nonneg (add_nonneg hx.le hy.le) hz.le) (sq_nonneg (y - z)),
      mul_nonneg (add_nonneg (add_nonneg hx.le hy.le) hz.le) (sq_nonneg (z - x)),
      mul_nonneg hx.le (sq_nonneg (y - z)), mul_nonneg hy.le (sq_nonneg (z - x)),
      mul_nonneg hz.le (sq_nonneg (x - y))]
  -- s ≤ xyz
  have h1 : x + y + z ≤ x * y * z := by nlinarith
  -- 27 s ≤ s^3
  have h2 : 27 * (x + y + z) ≤ (x + y + z)^3 := by nlinarith
  -- s^2 ≥ 27
  have h3 : 27 ≤ (x + y + z)^2 := by
    by_contra hc
    push_neg at hc
    have : (x + y + z)^3 < 27 * (x + y + z) := by
      have := mul_lt_mul_of_pos_left hc hs
      nlinarith
    linarith
  nlinarith
