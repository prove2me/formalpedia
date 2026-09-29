-- Prove2me | Theorems.Thm_WorkbookSource_problem_33411
-- name    : WorkbookSource.problem_33411
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:01:51.631783+00:00
-- url     : https://prove2.me/theorems/ce030976-e319-403e-a983-cb99e50f3c75
-- title:
--   Comparing a power with a sum of two powers
-- statement:
--   Which is larger?
--    \(101^{50}\) or \( (100^{50}+99^{50})\)
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_33411` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_33411; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_33411 : (101^50) > (100^50 + 99^50)  :=  by sorry
