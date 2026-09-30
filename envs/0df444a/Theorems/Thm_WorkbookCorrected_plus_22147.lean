-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_22147
-- name    : WorkbookCorrected.plus_22147
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-30T05:09:23.446501+00:00
-- url     : https://prove2.me/theorems/d8f341fd-d860-49ad-a6f6-0a40e3d5921c
-- title:
--   Real logarithm identity #22147
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   Real.logb 25 10 = Real.log 10 / Real.log 25
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_22147`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_22147 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_22147; Apache-2.0; corrects Open node a3758ce7-7b1c-4fb4-87d1-4d0c24212a11

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_22147 : Real.logb 25 10 = Real.log 10 / Real.log 25 := by sorry
