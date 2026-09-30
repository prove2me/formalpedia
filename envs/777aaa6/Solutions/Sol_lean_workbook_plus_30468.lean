-- Prove2me | solution 1 for lean_workbook_plus_30468
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:02:33.485945+00:00
-- url     : https://prove2.me/submissions/a5e6d606-84ea-4f63-973d-6f4e76088917

import Mathlib.Analysis.Complex.Basic

theorem solution (n : ℕ) : (4 * (4 * n + 3) * (4 * n + 1) / (3 * (3 * n + 2) * (3 * n + 1))) ≤ Real.sqrt 6 := by
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hden : (0:ℝ) < 3 * (3 * n + 2) * (3 * n + 1) := by positivity
  have h1 : (4 * (4 * (n:ℝ) + 3) * (4 * n + 1) / (3 * (3 * n + 2) * (3 * n + 1))) ≤ 64/27 := by
    rw [div_le_iff₀ hden]
    nlinarith
  have h2 : (64/27 : ℝ) ≤ Real.sqrt 6 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  linarith
