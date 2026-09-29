-- Prove2me | Theorems.Thm_lean_workbook_plus_36600
-- name    : lean_workbook_plus_36600
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/8fb169d0-35a5-4cbc-8091-588a5ee0a1e4
-- statement:
--   if $0\leq x \leq1$ then $g(x)=-2x^2+2x+2=-2(x-1/2)^2+\frac{5}4\leq\frac{5}4$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36600 (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) :
  -2 * x ^ 2 + 2 * x + 2 ≤ 5 / 4   :=  by sorry
