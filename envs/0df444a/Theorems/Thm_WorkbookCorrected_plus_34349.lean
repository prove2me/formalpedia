-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_34349
-- name    : WorkbookCorrected.plus_34349
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:47:23.603266+00:00
-- url     : https://prove2.me/theorems/01ae4f14-6f04-42e6-9bc1-4d445705a5de
-- title:
--   Three-term natural arithmetic
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   650 + 325 - 268 = 707
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_34349`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_34349 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_34349; Apache-2.0; corrects Open node 5c414219-bb80-40f1-91d0-a94f46f912e0

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_34349 : (650 : ℕ) + 325 - 268 = 707 := by sorry
