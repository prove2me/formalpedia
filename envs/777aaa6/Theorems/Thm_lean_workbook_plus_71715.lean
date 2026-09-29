-- Prove2me | Theorems.Thm_lean_workbook_plus_71715
-- name    : lean_workbook_plus_71715
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/81fafb82-ecbf-43da-a69d-d893f081f110
-- statement:
--   With $x, y$ be positive real numbers such that $xy-x=2$ . Prove that: $\frac{4}{x+y}+\frac{1}{y}\le\frac{3}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71715 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x * y - x = 2) : 4 / (x + y) + 1 / y ≤ 3 / 2   :=  by sorry
