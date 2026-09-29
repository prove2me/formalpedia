-- Prove2me | Theorems.Thm_lean_workbook_plus_17772
-- name    : lean_workbook_plus_17772
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/4c3b7943-6853-4989-bb5e-c1fb493b15b7
-- statement:
--   If $x+y+xy=1$ , where $x$ and $y$ are nonzero real numbers, find the value of $xy+\frac{1}{xy}-\frac{y}{x}-\frac{x}{y}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17772 (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y + x*y = 1) : x*y + 1/(x*y) - y/x - x/y = 4   :=  by sorry
