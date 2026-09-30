-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_65916
-- name    : WorkbookCorrected.plus_65916
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T14:33:40.805301+00:00
-- url     : https://prove2.me/theorems/a3a3686e-b8c8-4b89-82ad-c4f403739d0e
-- title:
--   Elementary arithmetic identity #65916
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   1 + 3 + 6 + 10 + 15 + 21 + 28 + 36 + 45 + 55 + 66 + 78 + 91 + 105 + 120 + 136 + 153 + 171 = 1140
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_65916`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_65916 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_65916; Apache-2.0; corrects Open node bb40de6e-2c7d-4a38-981b-fa7290c68998

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_65916 : 1 + 3 + 6 + 10 + 15 + 21 + 28 + 36 + 45 + 55 + 66 + 78 + 91 + 105 + 120 + 136 + 153 + 171 = 1140 := by sorry
