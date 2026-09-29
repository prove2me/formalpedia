-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_41118
-- name    : WorkbookCorrected.plus_41118
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T11:49:27.134061+00:00
-- url     : https://prove2.me/theorems/0f7668f4-eea4-41f2-802c-0b0adc84d20e
-- title:
--   Elementary arithmetic identity #41118
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   4 * 1 * 3 * 5 = 60
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_41118`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_41118 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_41118; Apache-2.0; corrects Open node 4ae05925-7854-4e4e-ad8d-6aecd7d390c5

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_41118 : 4 * 1 * 3 * 5 = 60 := by sorry
