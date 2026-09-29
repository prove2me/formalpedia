-- Prove2me | Theorems.Thm_WorkbookSource_problem_18637
-- name    : WorkbookSource.problem_18637
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:11:44.879787+00:00
-- url     : https://prove2.me/theorems/525c62c9-3ae0-4f08-bdd0-296fa545d429
-- title:
--   Solving a short integer equation
-- statement:
--   Find the value of $k$ in the equation $1^3+k+2-1+k-2=0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_18637` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_18637; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_18637 (k : ℤ) : 1^3+k+2-1+k-2=0 ↔ k = 0  :=  by sorry
