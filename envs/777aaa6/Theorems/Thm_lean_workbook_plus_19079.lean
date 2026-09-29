-- Prove2me | Theorems.Thm_lean_workbook_plus_19079
-- name    : lean_workbook_plus_19079
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/fe19dbe4-bf37-4505-8d95-6edee3cc6088
-- statement:
--   The polynomial sort of looks like $(x-1)^3.$ This polynomial expands out to: $x^3-3x^2+3x-1.$ At this point, we can hope that some things will come out nicely. For one, we like that $-1$ term, so if we're going to multiply this by something to get the given polynomial, it's going to be something like $(ax+1).$ Another things is to check the leading coefficient in the polynomial: it's $x^4.$ Because we have $x^3,$ we just need to multiply by $x$ to get what we want. Summing up, let's try multiplying $(x-1)^3$ by $(x+1).$ This gives: $$(x^4-3x^3+3x^2-x)+(x^3-3x^2+3x-1)=x^4-2x^2+2x-1.$$ Thus, we have: $$x^4-2x^3+2x-1=(x-1)^3(x+1).$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19079  (x : ℝ) :
  x^4 - 2 * x^3 + 2 * x - 1 = (x - 1)^3 * (x + 1)   :=  by sorry
