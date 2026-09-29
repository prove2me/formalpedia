-- Prove2me | Theorems.Thm_lean_workbook_plus_55013
-- name    : lean_workbook_plus_55013
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/e7af399a-e7ff-4d5e-8bb5-46cb8cde3a14
-- statement:
--   $(p - 1)^2 (4 p^3 + 6 p^2 + 9 p + 8) (2 p^4 + 10 p^3 + 9 p^2 + 16 p + 8)\geq 0$ . Done!
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55013 : ∀ p : ℝ, (p - 1) ^ 2 * (4 * p ^ 3 + 6 * p ^ 2 + 9 * p + 8) * (2 * p ^ 4 + 10 * p ^ 3 + 9 * p ^ 2 + 16 * p + 8) ≥ 0   :=  by sorry
