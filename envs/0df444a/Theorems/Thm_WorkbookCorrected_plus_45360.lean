-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_45360
-- name    : WorkbookCorrected.plus_45360
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-23T13:26:25.695251+00:00
-- url     : https://prove2.me/theorems/8ec3c6d5-edd2-4da5-9067-ecfff615e44a
-- title:
--   Rational arithmetic identity #45360
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (1/2)*(2/3) = 1/3
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_45360`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_45360 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_45360; Apache-2.0; corrects Open node 9f256360-fda1-4322-a3e5-0687dc900a6a

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_45360 : ((1:ℚ)/2)*(2/3) = (1:ℚ)/3 := by sorry
