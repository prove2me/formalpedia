-- Prove2me | Theorems.Thm_lean_workbook_plus_54225
-- name    : lean_workbook_plus_54225
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/f424c264-1dcc-496f-b586-62219cc9b1b0
-- statement:
--   For what values of $x$ is it true that $x^2 - 5x - 4 \le 10$ ? Express your answer in interval notation.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54225 (x : ℝ) : x^2 - 5*x - 4 ≤ 10 ↔ -2 ≤ x ∧ x ≤ 7   :=  by sorry
