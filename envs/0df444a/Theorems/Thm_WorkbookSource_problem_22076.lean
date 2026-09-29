-- Prove2me | Theorems.Thm_WorkbookSource_problem_22076
-- name    : WorkbookSource.problem_22076
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:40:27.18997+00:00
-- url     : https://prove2.me/theorems/c8c1e02e-b749-4b78-ada2-e2c173e852ad
-- title:
--   A polynomial sum of squares inequality
-- statement:
--   Prove that for any $x$ , $y$ and $z$
--
--    $x^4+1+y^4+z^2+2x^2\ge 2x^2y^2+2xz+2x$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_22076` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_22076; Apache-2.0

import Mathlib
open Real

theorem WorkbookSource.problem_22076 (x y z : ℝ) : x^4 + 1 + y^4 + z^2 + 2 * x^2 ≥ 2 * x^2 * y^2 + 2 * x * z + 2 * x  :=  by sorry
