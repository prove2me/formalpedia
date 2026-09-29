-- Prove2me | Theorems.Thm_WorkbookSource_problem_13032
-- name    : WorkbookSource.problem_13032
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T15:02:14.942851+00:00
-- url     : https://prove2.me/theorems/a294f92b-8e35-4d34-ae1b-e987e30f1448
-- title:
--   A coefficient sum from a polynomial value at one
-- statement:
--   Find $a+b+c+d$ given the function $f(x)=ax^3+bx^2+cx+d$ and the following conditions: $f(0)=4$, $f(1)=10$, $f(2)=26$, $f(-1)=2$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_13032` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_13032; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_13032 (a b c d : ℝ) (h₁ : a*0^3 + b*0^2 + c*0 + d = 4) (h₂ : a*1^3 + b*1^2 + c*1 + d = 10) (h₃ : a*2^3 + b*2^2 + c*2 + d = 26) (h₄ : a*(-1)^3 + b*(-1)^2 + c*(-1) + d = 2) : a + b + c + d = 10  :=  by sorry
