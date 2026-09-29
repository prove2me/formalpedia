-- Prove2me | Theorems.Thm_WorkbookSource_problem_12448
-- name    : WorkbookSource.problem_12448
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:46:55.248806+00:00
-- url     : https://prove2.me/theorems/cb93db73-c892-40f9-b300-afeab59bcf90
-- title:
--   Cancelling a common addend in an equation
-- statement:
--   Solve for $x$ in the equation $19 + x = 19$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_12448` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_12448; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_12448 (x : ℝ) (h : 19 + x = 19) : x = 0  :=  by sorry
