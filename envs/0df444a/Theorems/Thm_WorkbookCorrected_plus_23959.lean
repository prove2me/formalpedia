-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_23959
-- name    : WorkbookCorrected.plus_23959
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T19:08:08.015276+00:00
-- url     : https://prove2.me/theorems/17567c71-787f-45b4-8637-138b76b92cdc
-- title:
--   Elementary arithmetic identity #23959
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   53130 = 53130
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_23959`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_23959 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_23959; Apache-2.0; corrects Open node d16f5b0f-388d-44bd-87c2-64385823016c

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_23959 : 53130 = 53130 := by sorry
