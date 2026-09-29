-- Prove2me | Theorems.Thm_WorkbookSource_problem_32553
-- name    : WorkbookSource.problem_32553
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:01:49.982056+00:00
-- url     : https://prove2.me/theorems/382dcf98-f66c-4b64-b743-40792f91d829
-- title:
--   The last two digits of a product of powers
-- statement:
--   Find the last-two-digit of $ 13^{2009}\times9999^{6}\times3^{12}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_32553` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_32553; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_32553 : 13 ^ 2009 * 9999 ^ 6 * 3 ^ 12 ≡ 93 [MOD 100]  :=  by sorry
