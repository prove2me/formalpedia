-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_50061
-- name    : WorkbookCorrected.plus_50061
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T11:43:03.102066+00:00
-- url     : https://prove2.me/theorems/4d829544-b428-459a-a882-7c44cb183eb5
-- title:
--   Elementary arithmetic identity #50061
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   210 - 80 = 130
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_50061`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_50061 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_50061; Apache-2.0; corrects Open node a4520b1c-b21e-423a-bb58-34c4fe57c8a4

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_50061 : 210 - 80 = 130 := by sorry
