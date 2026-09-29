-- Prove2me | Theorems.Thm_WorkbookSource_problem_43314
-- name    : WorkbookSource.problem_43314
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:40:37.880569+00:00
-- url     : https://prove2.me/theorems/99d789a8-0ef3-4d9f-be59-467364282b01
-- title:
--   A quadratic bound from a determinant constraint
-- statement:
--   If real numbers $x,y,z$ satisfy $xy-z^2\ge1$, then
--
--   $$(x+2y)^2\ge(y+2z)^2+6.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_43314` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_43314; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_43314 (x y z : ℝ) (h : 1 ≤ x*y - z^2) : (x + 2*y)^2 ≥ (y + 2*z)^2 + 6  :=  by sorry
