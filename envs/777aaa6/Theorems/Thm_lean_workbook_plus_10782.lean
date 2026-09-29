-- Prove2me | Theorems.Thm_lean_workbook_plus_10782
-- name    : lean_workbook_plus_10782
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/12ff1bbb-f3bc-4ab5-a859-8e34a2c5e557
-- statement:
--   The equation is equivalent to: \n\n $$n^4=n^3+13n^2+36n+39$$ And in part a we have proved that $n$ must be a multiple of 3 to be a solution. So the LHS is divisible by 9 and each of the terms $n^3 , 13n^2 , 36n$ is divisible by 9. But 39 is not divisible by 9 so the RHS is not a multiple of 9. Contradiction. There is no solution in positive integers
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10782  (n : ℕ)
  (h₀ : 0 < n)
  (h₁ : 3∣n)
  (h₂ : n^4 = n^3 + 13 * n^2 + 36 * n + 39) :
  False   :=  by sorry
