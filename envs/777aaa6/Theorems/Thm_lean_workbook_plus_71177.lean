-- Prove2me | Theorems.Thm_lean_workbook_plus_71177
-- name    : lean_workbook_plus_71177
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/d35e14e5-8370-475d-a651-f76c1b3db4a0
-- statement:
--   Show that there exists a positive real number $x\neq 2$ such that $\log_2x=\frac{x}{2}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71177 : ∃ x : ℝ, 0 < x ∧ x ≠ 2 ∧ Real.logb 2 x = x / 2   :=  by sorry
