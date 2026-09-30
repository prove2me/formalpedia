-- Prove2me | solution 1 for lean_workbook_plus_13017
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T02:10:55.743378+00:00
-- url     : https://prove2.me/submissions/e26cf29d-1563-49be-b409-1cd3bcaaf21e

import Mathlib.Analysis.Complex.Basic

theorem solution (x y z : ℝ) (hx : x ∈ Set.Ioi 0) (hy : y ∈ Set.Ioi 0) (hz : z ∈ Set.Ioi 0) (h : x * y * z = 1) :
  x ^ 2 / (x ^ 2 + y ^ 2) + y ^ 2 / (y ^ 2 + z ^ 2) + z ^ 2 / (z ^ 2 + x ^ 2) ≤ 3 := by
  simp only [Set.mem_Ioi] at hx hy hz
  have h1 : x ^ 2 / (x ^ 2 + y ^ 2) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [sq_nonneg y]
  have h2 : y ^ 2 / (y ^ 2 + z ^ 2) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [sq_nonneg z]
  have h3 : z ^ 2 / (z ^ 2 + x ^ 2) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [sq_nonneg x]
  linarith
