-- Prove2me | Theorems.Thm_WorkbookSource_problem_5962
-- name    : WorkbookSource.problem_5962
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:39:50.411703+00:00
-- url     : https://prove2.me/theorems/1d860088-d1c5-4484-b1f9-bc9928fed87a
-- title:
--   Solving a three-variable linear system
-- statement:
--   Solve for A, B, and C in the system of equations:
--   $-4A-10B=0$
--   $10A-4B=\frac{1}{2}$
--   $8C=\frac{1}{2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_5962` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_5962; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_5962 (A B C : ℝ) : -4*A-10*B=0 ∧ 10*A-4*B=1/2 ∧ 8*C=1/2 ↔ A=5/116 ∧ B=-1/58 ∧ C=1/16  :=  by sorry
