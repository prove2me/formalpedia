-- Prove2me | Theorems.Thm_WorkbookSource_problem_53369
-- name    : WorkbookSource.problem_53369
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:09:12.225024+00:00
-- url     : https://prove2.me/theorems/fa9d7011-5062-4b16-99bc-21fc989aff08
-- title:
--   A strict quadratic bound from two comparisons
-- statement:
--   if $a> c\ ,\ b> d$ prove: $( a+b+c+d )^{2}> 8 ( ad+bc )$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_53369` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_53369; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_53369 (a b c d : ℝ) (h1 : a > c) (h2 : b > d) : (a + b + c + d)^2 > 8 * (a * d + b * c)  :=  by sorry
