-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_10133
-- name    : WorkbookCorrected.plus_10133
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T11:52:46.38327+00:00
-- url     : https://prove2.me/theorems/05a6ec7d-ceb4-4a5f-89e6-fcef847e9474
-- title:
--   Elementary arithmetic identity #10133
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (2 * 10 * 100) = (10 * 2 * 100)
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_10133`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_10133 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_10133; Apache-2.0; corrects Open node d44e5c87-1f67-4396-b9c5-302c1f97c886

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_10133 : (2 * 10 * 100) = (10 * 2 * 100) := by sorry
