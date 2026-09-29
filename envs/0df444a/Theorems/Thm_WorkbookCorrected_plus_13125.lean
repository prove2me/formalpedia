-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_13125
-- name    : WorkbookCorrected.plus_13125
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-23T13:26:56.394472+00:00
-- url     : https://prove2.me/theorems/18497eae-85e5-48fd-9996-b1bba35fb228
-- title:
--   Rational arithmetic identity #13125
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (1680 / (1680 + 448)) = (15 / 19)
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_13125`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_13125 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_13125; Apache-2.0; corrects Open node 6892b2cd-16be-4494-8208-bbebb3ed3f7e

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_13125 : ((1680:ℚ) / (1680 + 448)) = ((15:ℚ) / 19) := by sorry
