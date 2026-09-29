-- Prove2me | Theorems.Thm_WorkbookSource_problem_16058
-- name    : WorkbookSource.problem_16058
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:13:25.077043+00:00
-- url     : https://prove2.me/theorems/5eb38d31-f6f5-4e75-90e5-f04be8f07c81
-- title:
--   Comparing two powers of consecutive factorials
-- statement:
--   Greater of two numbers $(101!)^{100}$ or $(100!)^{101}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_16058` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_16058; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_16058 (x y : ℝ) (hx : x = (101!)^100) (hy : y = (100!)^101) : x > y  :=  by sorry
