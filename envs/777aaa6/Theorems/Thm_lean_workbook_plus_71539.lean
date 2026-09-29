-- Prove2me | Theorems.Thm_lean_workbook_plus_71539
-- name    : lean_workbook_plus_71539
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/0cf56ad1-945f-4c26-a76b-3ecd4628567d
-- statement:
--   But $\frac{(a+b)^2}{a+b-2}\geq8\Leftrightarrow(a+b-4)^2\geq0.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71539 (a b : ℝ) (hab : a + b > 2) : (a + b) ^ 2 / (a + b - 2) ≥ 8 ↔ (a + b - 4) ^ 2 ≥ 0   :=  by sorry
