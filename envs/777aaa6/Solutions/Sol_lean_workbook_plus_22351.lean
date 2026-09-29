-- Prove2me | solution 1 for lean_workbook_plus_22351
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-09T00:00:00.984745+00:00
-- url     : https://prove2.me/submissions/d87f673a-67ca-4208-ae8d-4e35402ca72e

import Theorems.Thm_lean_workbook_plus_22351

theorem solution (a b : ℝ) : (3 * a ^ 2 + b ^ 2) ^ 2 ≥ 0 := by
  exact sq_nonneg _
