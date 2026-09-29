-- Prove2me | Theorems.Thm_WorkbookSource_problem_33828
-- name    : WorkbookSource.problem_33828
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:59:35.915198+00:00
-- url     : https://prove2.me/theorems/979ad2f5-3699-4d81-9b3d-5745ba6b9aaf
-- title:
--   Comparing two large integer powers
-- statement:
--   The following strict numerical comparison holds:
--
--   $$ 2^{33}3^{10}>5^{21}. $$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_33828` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_33828; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_33828 : (2^(33)*3^(10) : ℝ) > 5^(21)  :=  by sorry
