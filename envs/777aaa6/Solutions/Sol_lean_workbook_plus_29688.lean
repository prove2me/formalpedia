-- Prove2me | solution 1 for lean_workbook_plus_29688
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:25:41.436461+00:00
-- url     : https://prove2.me/submissions/df413df2-ba51-4224-b3b8-d7514bd1d943

import Mathlib
set_option autoImplicit false

theorem solution (a b c x y z : ℝ) (hx : x = Real.sqrt (a ^ 2 + (b - c) ^ 2)) (hy : y = Real.sqrt (b ^ 2 + (c - a) ^ 2)) (hz : z = Real.sqrt (c ^ 2 + (a - b) ^ 2)) : x ^ 2 + y ^ 2 - z ^ 2 ≥ 0   := by
  have ha0 : 0 ≤ a^2 + (b-c)^2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hb0 : 0 ≤ b^2 + (c-a)^2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hc0 : 0 ≤ c^2 + (a-b)^2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  rw [hx, hy, hz, Real.sq_sqrt ha0, Real.sq_sqrt hb0, Real.sq_sqrt hc0]
  nlinarith only [sq_nonneg (a+b-c)]

#print axioms solution
