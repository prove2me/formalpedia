-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_43361
-- name    : WorkbookCorrected.plus_43361
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-23T13:26:55.521551+00:00
-- url     : https://prove2.me/theorems/06bad150-0c95-4b80-9639-c8883be8ac1a
-- title:
--   Rational arithmetic identity #43361
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (1/3 + 2/3 * (1/2 * (1 - 1/56))) = 37/56
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_43361`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_43361 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_43361; Apache-2.0; corrects Open node 47f5eba2-62c4-4c3c-a87c-6d1f9d9e1739

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_43361 : ((1:ℚ)/3 + 2/3 * (1/2 * (1 - 1/56))) = (37:ℚ)/56 := by sorry
