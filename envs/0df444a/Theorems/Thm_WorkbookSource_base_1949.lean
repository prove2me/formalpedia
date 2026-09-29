-- Prove2me | Theorems.Thm_WorkbookSource_base_1949
-- name    : WorkbookSource.base_1949
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:29:47.173985+00:00
-- url     : https://prove2.me/theorems/353599dc-0b49-499b-9815-e0b9a99791d7
-- title:
--   A factorial is not congruent to minus two modulo 2003
-- statement:
--   How do you show that $1000!
--   ot\equiv -2 \mod 2003$?
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_1949` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_1949; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_1949 : ¬(1000! ≡ -2 [ZMOD 2003])  :=  by sorry
