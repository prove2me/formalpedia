-- Prove2me | Theorems.Thm_WorkbookSource_problem_40020
-- name    : WorkbookSource.problem_40020
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:13:57.143024+00:00
-- url     : https://prove2.me/theorems/d45aabaf-3613-4f40-ab50-77e50fbb6dbe
-- title:
--   Factoring a difference of reciprocal sums
-- statement:
--   Let $x_1 > x_2>0$ , then $f(x_1)-f(x_2)=x_1-x_2+\dfrac{1}{x_1}-\dfrac{1}{x_2}=\dfrac{(x_1-x_2)(x_1x_2-1)}{x_1x_2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_40020` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_40020; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_40020  (x1 x2 : ℝ)
  (f : ℝ → ℝ)
  (h₀ : 0 < x1 ∧ 0 < x2)
  (h₁ : x1 > x2)
  (h₂ : f x1 - f x2 = x1 - x2 + (1 / x1 - 1 / x2)) :
  f x1 - f x2 = (x1 - x2) * (x1 * x2 - 1) / (x1 * x2)  :=  by sorry
