-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_13311
-- name    : WorkbookCorrected.plus_13311
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T12:44:55.603729+00:00
-- url     : https://prove2.me/theorems/42418fae-e5f9-46fc-8717-39c66c0c2f9a
-- title:
--   Elementary arithmetic identity #13311
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   0 + 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 + 11 + 12 = 78
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_13311`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_13311 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_13311; Apache-2.0; corrects Open node 0cc382b2-5442-4618-94f0-4a0b8398c599

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_13311 : 0 + 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 + 11 + 12 = 78 := by sorry
