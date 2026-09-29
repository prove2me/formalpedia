-- Prove2me | solution 1 for lean_workbook_plus_72979
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-09T01:32:00.366856+00:00
-- url     : https://prove2.me/submissions/b072f0f7-5296-48ae-a7b1-79bd968972c4

import Theorems.Thm_lean_workbook_plus_72979
import Mathlib.Tactic.Linarith

theorem solution : ∀ x ≥ 0, 2 * x ^ 3 - 3 * x ^ 2 + 1 ≥ 0 := by
  intro x hx
  nlinarith [mul_nonneg (sq_nonneg (x - 1)) hx, sq_nonneg (x - 1), hx]
