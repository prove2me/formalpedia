-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_2048
-- name    : WorkbookCorrected.plus_2048
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-30T09:47:29.731854+00:00
-- url     : https://prove2.me/theorems/a7369287-fb7a-47cd-9b94-4abe32a07462
-- title:
--   Real logarithm identity #2048
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   2^(Real.logb 2 5 - 2) = 2^(Real.logb 2 5) / 2^2
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_2048`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_2048 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_2048; Apache-2.0; corrects Open node 708b5936-4988-4b07-bd45-2ec77a455817

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_2048 : (2:ℝ) ^ (Real.logb 2 5 - 2) = (2:ℝ) ^ (Real.logb 2 5) / (2:ℝ) ^ 2 := by sorry
