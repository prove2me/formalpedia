-- Prove2me | Theorems.Thm_WorkbookSource_problem_7992
-- name    : WorkbookSource.problem_7992
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:46:02.029+00:00
-- url     : https://prove2.me/theorems/2fb4fdde-1673-43c8-8d9c-59a37b799af7
-- title:
--   Solving a linear nonnegative inequality
-- statement:
--   We also have $2x+1\geq 0$ $x\geq -\frac12$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_7992` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_7992; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_7992 (x:ℝ) : 2*x+1 >= 0 ↔ x >= -1/2  :=  by sorry
