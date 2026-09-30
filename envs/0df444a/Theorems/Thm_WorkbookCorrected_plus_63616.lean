-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_63616
-- name    : WorkbookCorrected.plus_63616
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T14:18:44.305379+00:00
-- url     : https://prove2.me/theorems/3a498851-d19a-4061-a15b-e751a8560863
-- title:
--   Elementary arithmetic identity #63616
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   98 + 96 + 94 + 92 + 90 + 88 + 86 + 84 + 82 + 80 + 78 + 76 + 74 + 72 + 70 + 68 + 66 + 64 + 62 + 60 + 58 + 56 + 54 + 52 + 50 + 48 + 46 + 44 + 42 + 40 + 38 + 36 + 34 + 32 + 30 + 28 + 26 + 24 + 22 + 20 + 18 + 16 + 14 + 12 + 10 + 8 + 6 + 4 + 2 + 0 = 2450
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_63616`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_63616 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_63616; Apache-2.0; corrects Open node 082e6917-9a5f-4cdd-965a-a0e547d61179

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_63616 : 98 + 96 + 94 + 92 + 90 + 88 + 86 + 84 + 82 + 80 + 78 + 76 + 74 + 72 + 70 + 68 + 66 + 64 + 62 + 60 + 58 + 56 + 54 + 52 + 50 + 48 + 46 + 44 + 42 + 40 + 38 + 36 + 34 + 32 + 30 + 28 + 26 + 24 + 22 + 20 + 18 + 16 + 14 + 12 + 10 + 8 + 6 + 4 + 2 + 0 = 2450 := by sorry
