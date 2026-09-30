-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_33971
-- name    : WorkbookCorrected.plus_33971
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T14:36:47.847474+00:00
-- url     : https://prove2.me/theorems/26866eb5-9932-4751-96bb-9cc87fd3a0e0
-- title:
--   Elementary arithmetic identity #33971
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   1019090 = 1019090
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_33971`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_33971 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_33971; Apache-2.0; corrects Open node de645619-af4d-4d40-8520-627b2ae4e714

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_33971 : 1019090 = 1019090 := by sorry
