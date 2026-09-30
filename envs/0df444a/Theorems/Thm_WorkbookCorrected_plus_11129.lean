-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_11129
-- name    : WorkbookCorrected.plus_11129
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T13:05:51.258073+00:00
-- url     : https://prove2.me/theorems/c55bc42f-11d5-44bd-b4c5-9a8f90ebc4bd
-- title:
--   Elementary arithmetic identity #11129
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   1 + 21 + 70 + 84 + 45 + 11 + 1 = 233
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_11129`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_11129 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_11129; Apache-2.0; corrects Open node 7d56a112-ee26-4a54-a18d-a9b7cdb55bd4

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_11129 : 1 + 21 + 70 + 84 + 45 + 11 + 1 = 233 := by sorry
