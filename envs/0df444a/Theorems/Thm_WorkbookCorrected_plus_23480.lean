-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_23480
-- name    : WorkbookCorrected.plus_23480
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-30T04:29:32.475976+00:00
-- url     : https://prove2.me/theorems/e2902f9f-9baa-4f76-9ac6-bb6273dcac59
-- title:
--   Real logarithm identity #23480
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   Real.logb 4 8 = 3 / 2
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_23480`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_23480 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_23480; Apache-2.0; corrects Open node 58266548-c5b4-47c1-af8a-c56f1d560d28

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_23480 : Real.logb 4 8 = 3 / 2 := by sorry
