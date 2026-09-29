-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_65348
-- name    : WorkbookCorrected.plus_65348
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:43:03.942477+00:00
-- url     : https://prove2.me/theorems/82abd7a2-1447-4a5b-8a8e-7fb5c45865ae
-- title:
--   Three factorial times six
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   3!\cdot 2\cdot 3 = 36
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_65348`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_65348 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_65348; Apache-2.0; corrects Open node 2425cbe5-1089-4207-aaf0-a803d4fd59ba

import Mathlib.Data.Nat.Factorial.Basic

theorem WorkbookCorrected.plus_65348 : Nat.factorial 3 * 2 * 3 = 36 := by sorry
