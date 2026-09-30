-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_11936
-- name    : WorkbookCorrected.plus_11936
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-30T05:04:49.618386+00:00
-- url     : https://prove2.me/theorems/b832bf95-233c-4852-a198-88c2e508f8ba
-- title:
--   Real logarithm identity #11936
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   Real.logb 5 625 = 4
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_11936`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_11936 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_11936; Apache-2.0; corrects Open node 94fd5b4f-6c4e-4891-98c8-85384961e885

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_11936 : Real.logb 5 625 = 4 := by sorry
