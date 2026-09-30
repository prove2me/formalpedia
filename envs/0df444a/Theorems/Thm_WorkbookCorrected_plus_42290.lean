-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_42290
-- name    : WorkbookCorrected.plus_42290
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T13:36:01.840275+00:00
-- url     : https://prove2.me/theorems/276367be-51d2-4037-aed7-b62cd23e4d46
-- title:
--   Elementary arithmetic identity #42290
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   1 + 2 + 4 + 8 + 16 + 7 + 14 + 3 + 6 + 12 + 24 + 23 + 21 + 17 + 9 + 18 + 11 + 22 + 19 + 13 = 250
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_42290`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_42290 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_42290; Apache-2.0; corrects Open node f8d0f62a-6488-4a17-ba27-74f31d807f12

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_42290 : 1 + 2 + 4 + 8 + 16 + 7 + 14 + 3 + 6 + 12 + 24 + 23 + 21 + 17 + 9 + 18 + 11 + 22 + 19 + 13 = 250 := by sorry
