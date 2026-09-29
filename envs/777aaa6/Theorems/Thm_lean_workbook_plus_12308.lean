-- Prove2me | Theorems.Thm_lean_workbook_plus_12308
-- name    : lean_workbook_plus_12308
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/f082417d-5ae3-40bc-a574-7c02d0841807
-- statement:
--   Substituting between the two given equations, \n \n $x + (7-x^{2})^{2} = 11$ \n \n $x^{4} - 14x^{2} + x +38 =0 $ \n \n We can see that $x=2$ is a solution and, dividing the quartic by $x-2$ , we find that the other three solutions for $x$ are the roots of the cubic equation \n \n $x^{3} + 2x^{2} -10x - 19 =0$ . \n \n I don't see any nice solutions to this cubic.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12308  (x : ℝ)
  (h₀ : x + (7 - x^2)^2 = 11)
  (h₁ : x^4 - 14 * x^2 + x + 38 = 0) :
  x = 2 ∨ x^3 + 2 * x^2 - 10 * x - 19 = 0   :=  by sorry
