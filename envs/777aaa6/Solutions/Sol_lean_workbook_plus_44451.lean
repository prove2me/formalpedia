-- Prove2me | solution 1 for lean_workbook_plus_44451
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:06:23.555529+00:00
-- url     : https://prove2.me/submissions/882da000-411f-4e99-976c-8f4e9fb12ca9

import Mathlib.Analysis.Complex.Basic

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + y + z) ^ 2 * (x * y + y * z + z * x) ^ 2 ≤ 3 * (x ^ 2 + x * y + y ^ 2) * (z ^ 2 + z * x + x ^ 2) * (y ^ 2 + y * z + z ^ 2) := by
  -- Step 1: each quadratic factor dominates 3/4 of the square of the corresponding sum.
  have hA : 3 / 4 * (x + y) ^ 2 ≤ x ^ 2 + x * y + y ^ 2 := by nlinarith [sq_nonneg (x - y)]
  have hB : 3 / 4 * (z + x) ^ 2 ≤ z ^ 2 + z * x + x ^ 2 := by nlinarith [sq_nonneg (z - x)]
  have hC : 3 / 4 * (y + z) ^ 2 ≤ y ^ 2 + y * z + z ^ 2 := by nlinarith [sq_nonneg (y - z)]
  have hA0 : 0 ≤ 3 / 4 * (x + y) ^ 2 := by positivity
  have hB0 : 0 ≤ 3 / 4 * (z + x) ^ 2 := by positivity
  have hC0 : 0 ≤ 3 / 4 * (y + z) ^ 2 := by positivity
  have hAB : 3 / 4 * (x + y) ^ 2 * (3 / 4 * (z + x) ^ 2) ≤ (x ^ 2 + x * y + y ^ 2) * (z ^ 2 + z * x + x ^ 2) :=
    mul_le_mul hA hB hB0 (by positivity)
  have hABC : 3 / 4 * (x + y) ^ 2 * (3 / 4 * (z + x) ^ 2) * (3 / 4 * (y + z) ^ 2)
      ≤ (x ^ 2 + x * y + y ^ 2) * (z ^ 2 + z * x + x ^ 2) * (y ^ 2 + y * z + z ^ 2) :=
    mul_le_mul hAB hC hC0 (by positivity)
  -- Step 2: (x+y)(y+z)(z+x) ≥ (8/9)(x+y+z)(xy+yz+zx).
  have hP : 8 / 9 * ((x + y + z) * (x * y + y * z + z * x)) ≤ (x + y) * (y + z) * (z + x) := by
    nlinarith [mul_nonneg hx.le (sq_nonneg (y - z)), mul_nonneg hy.le (sq_nonneg (z - x)),
      mul_nonneg hz.le (sq_nonneg (x - y))]
  have hP0 : 0 ≤ 8 / 9 * ((x + y + z) * (x * y + y * z + z * x)) := by positivity
  have hP2 : (8 / 9 * ((x + y + z) * (x * y + y * z + z * x))) ^ 2 ≤ ((x + y) * (y + z) * (z + x)) ^ 2 :=
    pow_le_pow_left₀ hP0 hP 2
  nlinarith [hABC, hP2]
