-- Prove2me | Theorems.Thm_lean_workbook_plus_7240
-- name    : lean_workbook_plus_7240
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/34f02921-91cb-4ece-8833-422fcad345f7
-- statement:
--   $\sin{x}\sin{y}=\frac{1}{2}\cdot\left[\cos{\left(x-y\right)}-\cos{\left(x+y\right)}\right]$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7240 : ∀ x y : ℝ, sin x * sin y = 1 / 2 * (cos (x - y) - cos (x + y))   :=  by sorry
