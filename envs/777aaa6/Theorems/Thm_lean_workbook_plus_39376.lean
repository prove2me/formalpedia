-- Prove2me | Theorems.Thm_lean_workbook_plus_39376
-- name    : lean_workbook_plus_39376
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/caa30e5c-d7d2-404d-bd96-29c24378665f
-- statement:
--   if $-1\leq x \leq0$ then $g(x)=-2x^2-2x+2=-2(x+1/2)^2+\frac{5}4\leq\frac{5}4$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39376 (x : ℝ) (hx : -1 ≤ x ∧ x ≤ 0) :
  -2 * x ^ 2 - 2 * x + 2 ≤ 5 / 4   :=  by sorry
