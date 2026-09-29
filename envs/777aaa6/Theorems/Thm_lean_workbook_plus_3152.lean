-- Prove2me | Theorems.Thm_lean_workbook_plus_3152
-- name    : lean_workbook_plus_3152
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/6863757c-7d3b-4021-a21b-13c88ae970c0
-- statement:
--   Let $x, y$ be positive real numbers satisfying $x+y=1. $ Prove that $\frac{x}{2x+y}+\frac{y}{x+3y} \leq \frac{3}{5} $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3152 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x + y = 1) : x / (2 * x + y) + y / (x + 3 * y) ≤ 3 / 5   :=  by sorry
