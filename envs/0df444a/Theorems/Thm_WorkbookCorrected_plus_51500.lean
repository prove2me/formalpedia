-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_51500
-- name    : WorkbookCorrected.plus_51500
-- status  : Disproved
-- author  : @carlok
-- created : 2026-09-30T09:53:26.011962+00:00
-- url     : https://prove2.me/theorems/559ac8c0-df70-4455-8af8-ac415ae13895
-- title:
--   Elementary arithmetic identity #51500
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   4 + 4 + 2 = 8
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_51500`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_51500 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_51500; Apache-2.0; corrects Open node 0b35bf15-d5e9-4139-9e8c-edf6954967ac

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_51500 : 4 + 4 + 2 = 8 := by sorry
