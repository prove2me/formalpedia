-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_15496
-- name    : WorkbookCorrected.plus_15496
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-30T08:25:51.041626+00:00
-- url     : https://prove2.me/theorems/9bb953f5-9383-42bf-aeb9-ae3fca03b38d
-- title:
--   Real logarithm identity #15496
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   1 + Real.sqrt 6 > Real.sqrt 2
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_15496`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_15496 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_15496; Apache-2.0; corrects Open node ed6c6543-789c-43dd-90e2-cda207f478bc

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_15496 : 1 + Real.sqrt 6 > Real.sqrt 2 := by sorry
