-- Prove2me | Theorems.Thm_lean_workbook_plus_6452
-- name    : lean_workbook_plus_6452
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/6e8b5788-c5ba-424f-9afd-e8641f6d838f
-- statement:
--   equivalent to $\frac{(x-y)^2 \left(x^2 y^3+2 x+y\right)}{y^3}\geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6452 : ∀ x y : ℝ, (x - y) ^ 2 * (x ^ 2 * y ^ 3 + 2 * x + y) / y ^ 3 ≥ 0   :=  by sorry
