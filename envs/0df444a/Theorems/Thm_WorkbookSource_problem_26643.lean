-- Prove2me | Theorems.Thm_WorkbookSource_problem_26643
-- name    : WorkbookSource.problem_26643
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:36:45.347483+00:00
-- url     : https://prove2.me/theorems/567da785-0224-412c-8035-b23fd08ac9db
-- title:
--   Solving a natural-number equation
-- statement:
--   Find the value of $x$ in the equation $2x + 5 = 17$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_26643` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_26643; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_26643 (x : ℕ) (h : 2 * x + 5 = 17) : x = 6  :=  by sorry
