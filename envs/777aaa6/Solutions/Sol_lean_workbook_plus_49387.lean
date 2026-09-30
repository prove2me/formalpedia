-- Prove2me | solution 1 for lean_workbook_plus_49387
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:42:29.995387+00:00
-- url     : https://prove2.me/submissions/e5aba58b-f523-4d35-8ed0-17d94ef2e811

import Mathlib.Analysis.Complex.Basic

theorem solution (n : ℕ) : √((20 * 21 * 22 * 23) + 1) = 461 := by
  have h : ((20:ℝ) * 21 * 22 * 23 + 1) = 461 ^ 2 := by norm_num
  rw [h, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 461)]
