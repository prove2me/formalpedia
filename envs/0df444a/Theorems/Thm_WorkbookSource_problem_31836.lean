-- Prove2me | Theorems.Thm_WorkbookSource_problem_31836
-- name    : WorkbookSource.problem_31836
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:58:57.22444+00:00
-- url     : https://prove2.me/theorems/33702375-6ec8-4f7b-9eea-0368f112f7e2
-- title:
--   Factoring a quadratic polynomial
-- statement:
--   For given problem, you have $ac=8$ and $bd=-5$ , Thus, $abcd=-40$ . Now, it's easy to regroup it as $ad=-20$ and $bc=2$ to make $ad+bc=-18$ . Now, $8x^2-18x-5=8x^2-20x+2x-5=(8x^2-20x)+(2x-5)=4x(2x-5)+(2x-5)=(2x-5)(4x+1)$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_31836` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_31836; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_31836  (a b c d x : ℝ)
  (h₀ : a * c = 8)
  (h₁ : b * d = -5)
  (h₂ : (a * d + b * c) = -18)
  (h₃ : x = (a + b) * (c + d)) :
  8 * x^2 - 18 * x - 5 = (2 * x - 5) * (4 * x + 1)  :=  by sorry
