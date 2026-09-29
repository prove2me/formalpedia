-- Prove2me | Theorems.Thm_WorkbookSource_plus_63997
-- name    : WorkbookSource.plus_63997
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:11:16.521839+00:00
-- url     : https://prove2.me/theorems/856ace1b-36f3-4c21-9aa6-8923d957452c
-- title:
--   Strict increase of a difference of large powers
-- statement:
--   Prove that if $x>2000$ , then $x^{2000}-x^{1999}>{2000}^{2000}-2000^{1999}$ ?
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_63997` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_63997; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_63997 (x : ℝ) (hx : x > 2000) : x^2000 - x^1999 > 2000^2000 - 2000^1999   :=  by sorry
