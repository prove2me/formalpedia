-- Prove2me | Theorems.Thm_WorkbookSource_problem_2545
-- name    : WorkbookSource.problem_2545
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:39:31.383329+00:00
-- url     : https://prove2.me/theorems/36590dc0-a34c-4694-b11e-459720527d1e
-- title:
--   Evaluating a cubic subject to a quadratic relation
-- statement:
--   Find the value of $2x^{3}-3x^{2}-11x+8$ if when $x^{2}-3x-1=0$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_2545` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_2545; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_2545 (x : ℝ) (hx : x^2 - 3*x - 1 = 0) : 2*x^3 - 3*x^2 - 11*x + 8 = 11  :=  by sorry
