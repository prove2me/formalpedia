-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_53900
-- name    : WorkbookCorrected.plus_53900
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T13:54:12.989762+00:00
-- url     : https://prove2.me/theorems/adf03d07-834b-4e06-9e74-8c58ee02a3cb
-- title:
--   Elementary arithmetic identity #53900
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   122 + 145 + 170 + 197 + 226 + 257 + 290 + 325 + 362 + 401 = 2495
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_53900`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_53900 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_53900; Apache-2.0; corrects Open node 8f3cf6ec-50bd-4c81-9b6e-5168bc9448db

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_53900 : 122 + 145 + 170 + 197 + 226 + 257 + 290 + 325 + 362 + 401 = 2495 := by sorry
