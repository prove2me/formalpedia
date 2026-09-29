-- Prove2me | Theorems.Thm_WorkbookSource_problem_55362
-- name    : WorkbookSource.problem_55362
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:40:48.66543+00:00
-- url     : https://prove2.me/theorems/884e877e-dbdf-45cf-829c-579afb983043
-- title:
--   A specified quadratic value modulo411
-- statement:
--   For $a=b=137$, is $5(a+b)^2 + ab$ divisible by 411?
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_55362` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_55362; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_55362 : 5 * (137 + 137) ^ 2 + 137 * 137 ≡ 0 [ZMOD 411]  :=  by sorry
