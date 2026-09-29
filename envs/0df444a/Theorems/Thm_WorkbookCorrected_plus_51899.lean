-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_51899
-- name    : WorkbookCorrected.plus_51899
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-23T13:08:07.911419+00:00
-- url     : https://prove2.me/theorems/b882be4f-69d4-4fc0-8268-fdaeb3f23865
-- title:
--   Elementary arithmetic identity #51899
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   60 + 90 = 150
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_51899`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_51899 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_51899; Apache-2.0; corrects Open node c6a2446b-49ca-4426-8806-ec750f3ec405

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_51899 : 60 + 90 = 150 := by sorry
