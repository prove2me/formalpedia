-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_15957
-- name    : WorkbookCorrected.plus_15957
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-30T07:04:50.717181+00:00
-- url     : https://prove2.me/theorems/65cd88b8-088a-4bcb-801b-e82e9faf5838
-- title:
--   Real logarithm identity #15957
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   Real.logb 5 10 < 3 / 2
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_15957`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_15957 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_15957; Apache-2.0; corrects Open node 7a6bbe4f-bdd9-4a17-9188-af6bc97126b7

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_15957 : Real.logb 5 10 < 3 / 2 := by sorry
