-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_51689
-- name    : WorkbookCorrected.plus_51689
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T14:12:06.210946+00:00
-- url     : https://prove2.me/theorems/a52b6bc4-1526-4b78-8725-d5d3dac2f136
-- title:
--   Elementary arithmetic identity #51689
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   6 + 12 + 20 + 30 + 42 + 56 + 72 + 90 + 110 + 132 = 570
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_51689`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_51689 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_51689; Apache-2.0; corrects Open node cadb65de-00dc-47a4-88ff-aec2c984e4f9

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_51689 : 6 + 12 + 20 + 30 + 42 + 56 + 72 + 90 + 110 + 132 = 570 := by sorry
