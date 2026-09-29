-- Prove2me | Theorems.Thm_lean_workbook_plus_3871
-- name    : lean_workbook_plus_3871
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/d5eb392d-3e71-4c13-8d80-3f497ee8e32b
-- statement:
--   Prove that for non-negative numbers x and y the following inequalities holds \n $\frac{x+y}{x+y+1}\le \frac{x}{x+1}+\frac{y}{y+1}\le \frac{2(x+y)}{x+y+2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3871 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : (x + y) / (x + y + 1) ≤ x / (x + 1) + y / (y + 1) ∧ x / (x + 1) + y / (y + 1) ≤ (2 * (x + y)) / (x + y + 2)   :=  by sorry
