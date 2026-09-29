-- Prove2me | Theorems.Thm_WorkbookSource_problem_1481
-- name    : WorkbookSource.problem_1481
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:39:26.212434+00:00
-- url     : https://prove2.me/theorems/d5d6ed4e-9064-4dbf-b819-71bef87d89f5
-- title:
--   Converting a rational number to a terminating decimal
-- statement:
--   Express $\frac{23}{4}$ in decimal form.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_1481` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_1481; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_1481 (x : ℚ) (hx : x = 23/4) : x = 5.75  :=  by sorry
