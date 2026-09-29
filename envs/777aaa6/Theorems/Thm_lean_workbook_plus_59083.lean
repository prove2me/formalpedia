-- Prove2me | Theorems.Thm_lean_workbook_plus_59083
-- name    : lean_workbook_plus_59083
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/e5067262-690d-4bed-85e7-d8e87952cc7d
-- statement:
--   Let $x_1 > x_2>0$ , then $f(x_1)-f(x_2)=x_1-x_2+\dfrac{1}{x_1}-\dfrac{1}{x_2}=\dfrac{(x_1-x_2)(x_1x_2-1)}{x_1x_2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59083  (x1 x2 : ℝ)
  (h₀ : 0 < x1 ∧ 0 < x2)
  (h₁ : x1 > x2) :
  x1 - x2 + (1 / x1 - 1 / x2) = (x1 - x2) * (x1 * x2 - 1) / (x1 * x2)   :=  by sorry
