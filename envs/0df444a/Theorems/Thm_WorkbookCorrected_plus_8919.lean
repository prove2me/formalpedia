-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_8919
-- name    : WorkbookCorrected.plus_8919
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T12:45:05.90917+00:00
-- url     : https://prove2.me/theorems/aff6353b-cbfc-4dea-a7c6-1dde36e5e955
-- title:
--   Elementary arithmetic identity #8919
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   1 + 4 + 9 + 16 = 30
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_8919`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_8919 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_8919; Apache-2.0; corrects Open node 7c39b4af-900c-4dcc-b555-e712cc9aca9e

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_8919 : 1 + 4 + 9 + 16 = 30 := by sorry
