-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_22403
-- name    : WorkbookCorrected.plus_22403
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T13:37:58.179451+00:00
-- url     : https://prove2.me/theorems/0b93c2a0-6ff8-401c-906f-709f870caded
-- title:
--   Elementary arithmetic identity #22403
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   25 + 23 + 21 + 19 + 17 + 15 + 13 + 11 + 9 + 7 + 5 + 3 + 1 = 169
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_22403`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_22403 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_22403; Apache-2.0; corrects Open node 2c69dd67-2e11-48f1-a673-766ff312d2f3

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_22403 : 25 + 23 + 21 + 19 + 17 + 15 + 13 + 11 + 9 + 7 + 5 + 3 + 1 = 169 := by sorry
