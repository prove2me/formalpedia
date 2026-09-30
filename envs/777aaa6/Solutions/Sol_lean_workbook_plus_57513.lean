-- Prove2me | solution 1 for lean_workbook_plus_57513
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:07:16.654791+00:00
-- url     : https://prove2.me/submissions/4e210adb-7797-4f3b-ad58-12f5487bd7ad

import Mathlib.Analysis.Complex.Basic

theorem solution (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : 64 * (x + y + z) ^ 6 ≥ (x ^ 2 + y * z) * (y ^ 2 + x * z) * (z ^ 2 + x * y) := by
  have hxy := mul_nonneg hx hy
  have hxz := mul_nonneg hx hz
  have hyz := mul_nonneg hy hz
  have h1 : x ^ 2 + y * z ≤ (x + y + z) ^ 2 := by nlinarith [sq_nonneg y, sq_nonneg z]
  have h2 : y ^ 2 + x * z ≤ (x + y + z) ^ 2 := by nlinarith [sq_nonneg x, sq_nonneg z]
  have h3 : z ^ 2 + x * y ≤ (x + y + z) ^ 2 := by nlinarith [sq_nonneg x, sq_nonneg y]
  have p1 : 0 ≤ x ^ 2 + y * z := by positivity
  have p2 : 0 ≤ y ^ 2 + x * z := by positivity
  have p3 : 0 ≤ z ^ 2 + x * y := by positivity
  have hs : 0 ≤ (x + y + z) ^ 2 := by positivity
  have h12 : (x ^ 2 + y * z) * (y ^ 2 + x * z) ≤ (x + y + z) ^ 2 * (x + y + z) ^ 2 :=
    mul_le_mul h1 h2 p2 hs
  have h123 : (x ^ 2 + y * z) * (y ^ 2 + x * z) * (z ^ 2 + x * y) ≤ (x + y + z) ^ 2 * (x + y + z) ^ 2 * (x + y + z) ^ 2 :=
    mul_le_mul h12 h3 p3 (by positivity)
  have h6 : (x + y + z) ^ 2 * (x + y + z) ^ 2 * (x + y + z) ^ 2 = (x + y + z) ^ 6 := by ring
  have h64 : (x + y + z) ^ 6 ≤ 64 * (x + y + z) ^ 6 := by
    have : 0 ≤ (x + y + z) ^ 6 := by positivity
    linarith
  rw [h6] at h123
  linarith
