-- Prove2me | Theorems.Thm_lean_workbook_plus_64102
-- name    : lean_workbook_plus_64102
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/212cf2c0-9038-4993-b4e6-1af0d40d4cb2
-- statement:
--   Let $ x$ be the number of hours it would take the men to meet. \n\n Then we get the distance $ 4x$ for the $ M$ man and $ \frac{x}{2}[4+\frac{x-1}{2}]$ for the second man. They travel a total of 72 miles together when they meet. So we have the equation \n\n $ 4x+\frac{x}{2}[4+\frac{x-1}{2}]=72$ \n\n $ 4x+2x+\frac{1}{4}x^2-\frac{1}{4}x=72$ \n\n $ 6x+\frac{1}{4}x^2-\frac{1}{4}x=72$ \n\n $ x^2-x+24=72$ \n\n $ x^2-x-48=0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64102  (x : ℝ)
  (h₀ : 0 < x)
  (h₁ : 4 * x + (x / 2) * (4 + (x - 1) / 2) = 72) :
  x^2 - x - 48 = 0   :=  by sorry
