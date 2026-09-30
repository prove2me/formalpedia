-- Prove2me | solution 1 for lean_workbook_plus_79300
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:02:02.026259+00:00
-- url     : https://prove2.me/submissions/86e28bc1-ad74-4bde-ad13-4e01b8cfec8b

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem holder_cubic_amgm (u v w : ℝ) (hs : 0 ≤ u + v + w) :
    3 * u * v * w ≤ u ^ 3 + v ^ 3 + w ^ 3 := by
  have hsq : 0 ≤ (u - v) ^ 2 + (v - w) ^ 2 + (w - u) ^ 2 :=
    add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)
  nlinarith only [mul_nonneg hs hsq]

theorem holder_cubic_product_nonnegative (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x + y) ^ 3 ≤ 2 * (x ^ 3 + 1) * (y ^ 3 + 1) := by
  have hxy := mul_nonneg hx hy
  have h1 := holder_cubic_amgm x (x * y) 1 (by linarith)
  have h2 := holder_cubic_amgm y (x * y) 1 (by linarith)
  nlinarith only [h1, h2]

theorem holder_cubic_product_attained :
    (1 + 1 : ℝ) ^ 3 = 2 * (1 ^ 3 + 1) * (1 ^ 3 + 1) := by
  ring

theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (x ^ 3 + 1) * (1 + y ^ 3) * (1 + 1) ≥ (x + y) ^ 3 := by
  nlinarith only [holder_cubic_product_nonnegative x y hx.le hy.le]

#print axioms solution
#print axioms holder_cubic_product_nonnegative
