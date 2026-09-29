-- Prove2me | Theorems.Thm_WorkbookSource_problem_24885
-- name    : WorkbookSource.problem_24885
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:52:14.163056+00:00
-- url     : https://prove2.me/theorems/6119fcb9-2bdf-4ad1-be6b-f6516e6b5212
-- title:
--   Adding two bivariate quadratics
-- statement:
--   Add $x^2 - 3xy - y^2$ and $2x^2 + 5xy - 4y^2$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_24885` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_24885; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_24885 (x y : ℝ) : x^2 - 3*x*y - y^2 + (2*x^2 + 5*x*y - 4*y^2) = 3*x^2 + 2*x*y - 5*y^2  :=  by sorry
