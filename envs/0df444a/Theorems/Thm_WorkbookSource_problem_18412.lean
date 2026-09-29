-- Prove2me | Theorems.Thm_WorkbookSource_problem_18412
-- name    : WorkbookSource.problem_18412
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:40:26.78453+00:00
-- url     : https://prove2.me/theorems/9b2bcdfb-4e5e-4e37-9a9b-d3537cdf82b2
-- title:
--   Evaluating a polynomial at the opposite input
-- statement:
--   If $f(x)=x^5+x^3+1$ and $f(a)=7$ , find $f(-a)$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_18412` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_18412; Apache-2.0

import Mathlib
open Real

theorem WorkbookSource.problem_18412 (f : ℝ → ℝ) (a : ℝ) (h₁ : f = fun x => x^5 + x^3 + 1) (h₂ : f a = 7) : f (-a) = -5  :=  by sorry
