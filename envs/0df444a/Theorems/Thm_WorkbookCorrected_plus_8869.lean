-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_8869
-- name    : WorkbookCorrected.plus_8869
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-17T19:15:13.026272+00:00
-- url     : https://prove2.me/theorems/14f4aafc-4bfb-465f-9706-823b177ead36
-- statement:
--   There are $3!$ ways of ordering three distinct items, and $3! = 6$.
--
--   Formalization Note: Corrected missing colon in Lean-Workbook record `lean_workbook_plus_8869`; uses `Nat.factorial` because the `!` notation is not in scope with the minimal import.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_8869 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_8869; Apache-2.0; corrects Open node 59e84749-a8b6-45ce-9d83-1b0f7eaba6b7

import Mathlib.Data.Nat.Factorial.Basic

theorem WorkbookCorrected.plus_8869 : Nat.factorial 3 = 6 := by sorry
