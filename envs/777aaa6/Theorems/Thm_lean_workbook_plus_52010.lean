-- Prove2me | Theorems.Thm_lean_workbook_plus_52010
-- name    : lean_workbook_plus_52010
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/7d144026-7e03-495a-b896-ee6a869b551d
-- statement:
--   Prove that for real numbers $x$ and $y$ , we have $\left(xy+x+y-1\right)^2\leq2\left(x^2+1\right)\left(y^2+1\right).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52010 (x y : ℝ) :
  (x * y + x + y - 1) ^ 2 ≤ 2 * (x ^ 2 + 1) * (y ^ 2 + 1)   :=  by sorry
