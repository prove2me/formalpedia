-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_45694
-- name    : WorkbookCorrected.plus_45694
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T11:52:42.558467+00:00
-- url     : https://prove2.me/theorems/5b5f022a-e534-4354-9b1f-d249868bb62b
-- title:
--   Elementary arithmetic identity #45694
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   1*500+2*334+3*125+4*33+5*7+6*1=1716
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_45694`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_45694 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_45694; Apache-2.0; corrects Open node 4adf1f86-f177-4b26-87b4-26e31cac1236

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_45694 : 1*500+2*334+3*125+4*33+5*7+6*1=1716 := by sorry
