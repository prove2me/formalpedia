-- Prove2me | Theorems.Thm_WorkbookSource_problem_41226
-- name    : WorkbookSource.problem_41226
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:22:14.50492+00:00
-- url     : https://prove2.me/theorems/e5f20be6-b7e6-4e10-904a-2fabf91bccbe
-- title:
--   Factoring a homogeneous quadratic equation over the complex numbers
-- statement:
--   For complex x,y, 2x²−3xy+y²=0 if and only if (x−y)(2x−y)=0.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_41226` (Apache-2.0). The complete source proposition and variable types are retained.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_41226; Apache-2.0

import Mathlib
open Complex

theorem WorkbookSource.problem_41226 : ∀ x y : ℂ, (2 * x ^ 2 - 3 * x * y + y ^ 2 = 0) ↔ (x - y) * (2 * x - y) = 0  :=  by sorry
