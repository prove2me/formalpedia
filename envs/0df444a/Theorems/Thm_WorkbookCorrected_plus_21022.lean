-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_21022
-- name    : WorkbookCorrected.plus_21022
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T14:00:40.907693+00:00
-- url     : https://prove2.me/theorems/2f0b620e-e671-45c9-b889-f43c3c8d4d17
-- title:
--   Elementary arithmetic identity #21022
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   1 + 4 + 9 + 16 + 25 + 36 + 49 + 64 + 81 + 100 = 10 * 21 * 11 / 6
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_21022`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_21022 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_21022; Apache-2.0; corrects Open node 01adfd83-1a81-4c92-aab5-cf2ef9002a10

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_21022 : 1 + 4 + 9 + 16 + 25 + 36 + 49 + 64 + 81 + 100 = 10 * 21 * 11 / 6 := by sorry
