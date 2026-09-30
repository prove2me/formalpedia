-- Prove2me | solution 1 for lean_workbook_plus_41976
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T02:10:57.0331+00:00
-- url     : https://prove2.me/submissions/e70d2a64-778d-44cf-8fc5-49019d94deb5

import Mathlib.Analysis.Complex.Basic

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x / y + y / z + z / x + 67 * x * y * z / ((x + y) * (y + z) * (z + x) + 4 * x * y * z)) ≥ 9 / 12 := by
  have h1 : 0 ≤ x / y := by positivity
  have h2 : 0 ≤ y / z := by positivity
  have h3 : 0 ≤ z / x := by positivity
  have h4 : 0 ≤ 67 * x * y * z / ((x + y) * (y + z) * (z + x) + 4 * x * y * z) := by positivity
  have key : 1 ≤ x / y ∨ 1 ≤ y / z ∨ 1 ≤ z / x := by
    rcases le_or_gt y x with h | h
    · left
      rw [le_div_iff₀ hy, one_mul]
      exact h
    · rcases le_or_gt z y with h' | h'
      · right; left
        rw [le_div_iff₀ hz, one_mul]
        exact h'
      · right; right
        rw [le_div_iff₀ hx, one_mul]
        linarith
  rcases key with k | k | k <;> linarith
