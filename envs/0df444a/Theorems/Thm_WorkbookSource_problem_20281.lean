-- Prove2me | Theorems.Thm_WorkbookSource_problem_20281
-- name    : WorkbookSource.problem_20281
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:50:13.679966+00:00
-- url     : https://prove2.me/theorems/f3596696-5622-46fa-bf17-711b65215f55
-- title:
--   Comparing two large integer powers
-- statement:
--   Which is the larger of the 2 numbers $100^{117}$ or $117^{100}$ ? No log tables allowed
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_20281` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_20281; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_20281 : 100^117 > 117^100  :=  by sorry
