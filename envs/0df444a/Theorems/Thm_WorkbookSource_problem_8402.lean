-- Prove2me | Theorems.Thm_WorkbookSource_problem_8402
-- name    : WorkbookSource.problem_8402
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:46:08.493904+00:00
-- url     : https://prove2.me/theorems/418e11d0-49ee-4160-9e0e-e8aa65a12087
-- title:
--   The intersection of two lines
-- statement:
--   What is the coordinate of the intersection of $y = 2x - 3$ and $y = -7x - 12$ ?
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_8402` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_8402; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_8402 (x y : ℝ) : (y = 2*x - 3 ∧ y = -7*x - 12) ↔ x = -1 ∧ y = -5  :=  by sorry
