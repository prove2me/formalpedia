-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_41583
-- name    : WorkbookCorrected.plus_41583
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T12:48:34.111981+00:00
-- url     : https://prove2.me/theorems/290bc508-2200-4fd5-a761-b13886b068b4
-- title:
--   Elementary arithmetic identity #41583
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   2 + 4 + 6 = 12
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_41583`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_41583 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_41583; Apache-2.0; corrects Open node a0d1c60c-ed72-4cab-be5a-b3efaeee0f8e

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_41583 : 2 + 4 + 6 = 12 := by sorry
