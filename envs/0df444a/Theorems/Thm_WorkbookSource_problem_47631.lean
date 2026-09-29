-- Prove2me | Theorems.Thm_WorkbookSource_problem_47631
-- name    : WorkbookSource.problem_47631
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:22:14.561997+00:00
-- url     : https://prove2.me/theorems/67525616-5885-4ae1-9786-56ea4ff78163
-- title:
--   Factoring a polynomial in a product of complex variables
-- statement:
--   For complex b,z, z²b²+zb−2=(bz−1)(bz+2).
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_47631` (Apache-2.0). The complete source proposition and variable types are retained.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_47631; Apache-2.0

import Mathlib
open Complex

theorem WorkbookSource.problem_47631 : ∀ b z:ℂ, z^2 * b^2 + z * b - 2 = (b * z - 1) * (b * z + 2)  :=  by sorry
