-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_4340
-- name    : WorkbookCorrected.plus_4340
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-30T04:29:37.799009+00:00
-- url     : https://prove2.me/theorems/fdd84b87-408d-43be-bc34-27db9661466d
-- title:
--   Real logarithm identity #4340
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   Real.logb 3 (2^102) = 102 * Real.logb 3 2
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_4340`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_4340 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_4340; Apache-2.0; corrects Open node 41bef039-b73a-4868-ab12-7fd1ddf8ebc2

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_4340 : Real.logb 3 (2 ^ 102) = 102 * Real.logb 3 2 := by sorry
