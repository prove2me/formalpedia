-- Prove2me | solution 1 for lean_workbook_plus_36993
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:23:04.704133+00:00
-- url     : https://prove2.me/submissions/9b3f29e0-0fac-4419-8e3b-6380c97fa25e

import Mathlib.Analysis.Complex.Basic

theorem solution (x y z : ℝ) (hx: 0 < x) (hy: 0 < y) (hz: 0 < z) (h : x^2 + y^3 + z^4 ≥ x^3 + y^4 + z^5) : x^3 + y^3 + z^3 ≤ 3 := by
  -- For t > 0 and k ≥ m: t^k (t-1) ≥ t^m (t-1). Hence the hypothesis gives
  -- Σ t^2 (t-1) ≤ 0, Σ t (t-1) ≤ 0, Σ (t-1) ≤ 0, i.e. Σt^3 ≤ Σt^2 ≤ Σt ≤ 3.
  have hy1 : y ^ 3 * (y - 1) ≥ y ^ 2 * (y - 1) := by nlinarith [mul_nonneg (sq_nonneg y) (sq_nonneg (y - 1))]
  have hz1 : z ^ 4 * (z - 1) ≥ z ^ 2 * (z - 1) := by
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg z) (sq_nonneg (z - 1))) (by linarith : (0:ℝ) ≤ z + 1)]
  have h2 : x ^ 2 * (x - 1) + y ^ 2 * (y - 1) + z ^ 2 * (z - 1) ≤ 0 := by nlinarith
  have hx2 : x ^ 2 * (x - 1) ≥ x * (x - 1) := by nlinarith [mul_nonneg hx.le (sq_nonneg (x - 1))]
  have hy2 : y ^ 2 * (y - 1) ≥ y * (y - 1) := by nlinarith [mul_nonneg hy.le (sq_nonneg (y - 1))]
  have hz2 : z ^ 2 * (z - 1) ≥ z * (z - 1) := by nlinarith [mul_nonneg hz.le (sq_nonneg (z - 1))]
  have h1 : x * (x - 1) + y * (y - 1) + z * (z - 1) ≤ 0 := by linarith
  have hx3 : x * (x - 1) ≥ (x - 1) := by nlinarith [sq_nonneg (x - 1)]
  have hy3 : y * (y - 1) ≥ (y - 1) := by nlinarith [sq_nonneg (y - 1)]
  have hz3 : z * (z - 1) ≥ (z - 1) := by nlinarith [sq_nonneg (z - 1)]
  have h0 : x + y + z ≤ 3 := by linarith
  nlinarith
