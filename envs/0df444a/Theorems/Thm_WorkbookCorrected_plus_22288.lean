-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_22288
-- name    : WorkbookCorrected.plus_22288
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-23T13:26:42.169868+00:00
-- url     : https://prove2.me/theorems/d37543a7-914c-4b53-b063-7d03dd744c7b
-- title:
--   Rational arithmetic identity #22288
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (5/9)*(3/7)*(1/3) = 5/63
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_22288`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_22288 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_22288; Apache-2.0; corrects Open node a9f52251-06e4-4d00-9426-261fd90a61da

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_22288 : ((5:ℚ)/9)*(3/7)*(1/3) = (5:ℚ)/63 := by sorry
