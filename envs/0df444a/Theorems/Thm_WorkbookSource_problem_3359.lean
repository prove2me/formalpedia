-- Prove2me | Theorems.Thm_WorkbookSource_problem_3359
-- name    : WorkbookSource.problem_3359
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:12:24.471636+00:00
-- url     : https://prove2.me/theorems/427a5760-40ed-42b0-9c25-8db817dcbb70
-- title:
--   Evaluating a mixed monomial at reciprocal numbers
-- statement:
--   If $x = \frac34$ and $y = \frac43$ , find the value of $\frac12x^6y^7$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_3359` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_3359; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_3359 (x y : ℝ) (hx : x = 3/4) (hy : y = 4/3) : (1/2)*x^6*y^7 = 2/3  :=  by sorry
