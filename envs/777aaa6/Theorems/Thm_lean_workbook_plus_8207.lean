-- Prove2me | Theorems.Thm_lean_workbook_plus_8207
-- name    : lean_workbook_plus_8207
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/2b2597c6-988f-4626-89ec-072fa3c5894d
-- statement:
--   The given expression equals: \n\n $ \left (x+\frac{1}{x} \right )\left (y+\frac{1}{y} \right )+\left (x-\frac{1}{x} \right )\left (y-\frac{1}{y} \right )\ = xy+\frac{y}{x}+\frac{x}{y}+\frac{1}{xy}+xy-\frac{y}{x}-\frac{x}{y}+\frac{1}{xy}\ =2xy+\frac{2}{xy}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8207  (x y : ℝ)
  (h₀ : x ≠ 0)
  (h₁ : y ≠ 0) :
  (x + 1/x) * (y + 1/y) + (x - 1/x) * (y - 1/y) = 2 * x * y + 2 / (x * y)   :=  by sorry
