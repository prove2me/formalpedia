-- Prove2me | Theorems.Thm_WorkbookSource_problem_3217
-- name    : WorkbookSource.problem_3217
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:10:54.765598+00:00
-- url     : https://prove2.me/theorems/7824b6c6-0578-4c84-a770-c593680d3582
-- title:
--   Two symmetric polynomial evaluations
-- statement:
--   What is $f(-2021)+f(2019)$ ?
--   $f(x)=x^5+5x^4+10x^3+10x^2-2x+1$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_3217` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_3217; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_3217 (f : ℤ → ℤ) (f_def : ∀ x, f x = x^5 + 5 * x^4 + 10 * x^3 + 10 * x^2 - 2 * x + 1) : f (-2021) + f (2019) = 14  :=  by sorry
