-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_23474
-- name    : WorkbookCorrected.plus_23474
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T11:52:46.2612+00:00
-- url     : https://prove2.me/theorems/4154e21d-aedc-4212-be31-2df8c8100f9f
-- title:
--   Elementary arithmetic identity #23474
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   9 * 1 + 90 * 2 + 900 * 3 + 1008 * 4 = 6921
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_23474`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_23474 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_23474; Apache-2.0; corrects Open node 173b2999-8440-401c-8973-a812e8fb8808

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_23474 : 9 * 1 + 90 * 2 + 900 * 3 + 1008 * 4 = 6921 := by sorry
