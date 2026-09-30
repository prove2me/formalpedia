-- Prove2me | solution 1 for lean_workbook_plus_8058
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:06:28.689912+00:00
-- url     : https://prove2.me/submissions/e9ec5aeb-450a-4ed3-b1b6-27151d630608

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c x y z : ℝ) (ha : a ≥ 4) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b ≤ 2 * c) : (a - 3) * (b - x ^ 2 - y ^ 2 - z ^ 2) ≤ (c - x - y - z) ^ 2 := by
  -- Quadratic mean bound: 3(x²+y²+z²) ≥ (x+y+z)².
  have h1 : (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  -- AM-GM consequence: c² ≥ ab.
  have h2 : a * b ≤ c ^ 2 := by
    nlinarith [sq_nonneg (a - b), mul_nonneg (sub_nonneg.mpr hab) (by linarith : (0:ℝ) ≤ a + b + 2 * c)]
  have ha3 : (0:ℝ) ≤ a - 3 := by linarith
  have ha0 : (0:ℝ) < a := by linarith
  -- Replace the sum of squares by its lower bound.
  have h3 : (a - 3) * (b - x ^ 2 - y ^ 2 - z ^ 2) ≤ (a - 3) * (b - (x + y + z) ^ 2 / 3) :=
    mul_le_mul_of_nonneg_left (by linarith) ha3
  -- Key identity: a·[(c-s)² - (a-3)(b - s²/3)] = (as - 3c)²/3 + (a-3)(c² - ab).
  have h4 : 0 ≤ a * ((c - (x + y + z)) ^ 2 - (a - 3) * (b - (x + y + z) ^ 2 / 3)) := by
    nlinarith [sq_nonneg (a * (x + y + z) - 3 * c), mul_nonneg ha3 (sub_nonneg.mpr h2)]
  have h5 : 0 ≤ (c - (x + y + z)) ^ 2 - (a - 3) * (b - (x + y + z) ^ 2 / 3) := by
    by_contra hneg
    push_neg at hneg
    nlinarith [mul_pos ha0 (neg_pos.mpr hneg)]
  have h6 : (c - x - y - z) ^ 2 = (c - (x + y + z)) ^ 2 := by ring
  rw [h6]
  linarith
