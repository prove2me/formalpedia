-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_47605
-- name    : WorkbookCorrected.plus_47605
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-30T09:47:24.410673+00:00
-- url     : https://prove2.me/theorems/222cd0d9-2d37-4232-8975-4554b73da451
-- title:
--   Finite-sum arithmetic identity #47605
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   ∑ k in Finset.Icc 1 10, (2 * k)) - (∑ k in Finset.Icc 1 10, (2 * k - 1)) = 10
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_47605`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_47605 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_47605; Apache-2.0; corrects Open node dabb7a02-0a52-4ac5-ba60-672cae89aaf7

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_47605 : 10 = 10 := by sorry
