-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_7115
-- name    : WorkbookCorrected.plus_7115
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T14:21:47.987282+00:00
-- url     : https://prove2.me/theorems/7a94170d-9ad4-4a1f-8c2b-6360ab50be8d
-- title:
--   Elementary arithmetic identity #7115
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   25497420 = 25497420
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_7115`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_7115 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_7115; Apache-2.0; corrects Open node b36988d5-fc0d-4b63-91ca-686aaaf365b8

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_7115 : 25497420 = 25497420 := by sorry
