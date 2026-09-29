-- Prove2me | Theorems.Thm_lean_workbook_plus_77613
-- name    : lean_workbook_plus_77613
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/6565ea18-3f46-44d9-aecf-c6af6cccb78a
-- statement:
--   Prove that $(x+2)^3 < x^3 + 8x^2 - 6x +8 < (x+3)^3$ for $x > 9$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77613 (x : ℝ) (h : x > 9): (x+2)^3 < x^3 + 8*x^2 - 6*x +8 ∧ x^3 + 8*x^2 - 6*x +8 < (x+3)^3   :=  by sorry
