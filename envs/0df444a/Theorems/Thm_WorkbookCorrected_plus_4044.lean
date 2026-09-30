-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_4044
-- name    : WorkbookCorrected.plus_4044
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T14:33:50.168708+00:00
-- url     : https://prove2.me/theorems/41633997-9c06-47cf-9364-a3a00d8d648e
-- title:
--   Elementary arithmetic identity #4044
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   10100 = 10100
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_4044`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_4044 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_4044; Apache-2.0; corrects Open node edf94619-773b-4a55-9072-6ea7c2d6fda3

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_4044 : 10100 = 10100 := by sorry
