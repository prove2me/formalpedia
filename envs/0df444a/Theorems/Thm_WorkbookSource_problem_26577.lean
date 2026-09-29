-- Prove2me | Theorems.Thm_WorkbookSource_problem_26577
-- name    : WorkbookSource.problem_26577
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:52:31.486432+00:00
-- url     : https://prove2.me/theorems/0a16a24d-ed89-49b7-bb39-f0bc8b0b730f
-- title:
--   Simplifying a polynomial expression
-- statement:
--   $ f(x)=x^{2}+(x^{2}-1)+(2-2x)+2x-7=2x^{2}-6$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_26577` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_26577; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_26577 (x : ℝ) : x^2 + (x^2 - 1) + (2 - 2*x) + 2*x - 7 = 2*x^2 - 6  :=  by sorry
