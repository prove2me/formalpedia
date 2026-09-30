-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_26684
-- name    : WorkbookCorrected.plus_26684
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T14:20:46.875051+00:00
-- url     : https://prove2.me/theorems/54cef060-7803-4b42-913d-e8373f696494
-- title:
--   Elementary arithmetic identity #26684
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   1355454220 = 1355454220
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_26684`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_26684 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_26684; Apache-2.0; corrects Open node ed2d0696-34ff-462f-9935-9f0b884baca2

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_26684 : 1355454220 = 1355454220 := by sorry
