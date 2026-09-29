-- Prove2me | Theorems.Thm_lean_workbook_plus_4047
-- name    : lean_workbook_plus_4047
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/045fc4b5-9ceb-468d-8e98-807754afcf6b
-- statement:
--   The equation of this line is $y=\frac15x+b$ . Plugging in $(12,10)$ , we find $b=\frac{38}5$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4047  (x y : ℝ)
  (h₀ : x = 12)
  (h₁ : y = 10)
  (h₂ : y = 1 / 5 * x + b)
  (h₃ : b = 38 / 5) :
  y = 1 / 5 * x + b   :=  by sorry
