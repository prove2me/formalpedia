-- Prove2me | Theorems.Thm_lean_workbook_plus_77357
-- name    : lean_workbook_plus_77357
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/0969f225-1f39-4803-9e61-5a3089af9b76
-- statement:
--   After homogenization it is: \n $\sum_{cyc}\big( a^2+3bc-b^2-3ca \big)^2\ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77357 (a b c : ℝ) : (a^2 + 3 * b * c - b^2 - 3 * c * a)^2 + (b^2 + 3 * c * a - c^2 - 3 * a * b)^2 + (c^2 + 3 * a * b - a^2 - 3 * b * c)^2 ≥ 0   :=  by sorry
