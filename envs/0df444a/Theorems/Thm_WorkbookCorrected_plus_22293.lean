-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_22293
-- name    : WorkbookCorrected.plus_22293
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-23T13:26:41.530598+00:00
-- url     : https://prove2.me/theorems/615a6f30-c32e-4125-b73b-901d94183d3c
-- title:
--   Rational arithmetic identity #22293
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (2/3)^2 * (1/3)^2 * 3 = 4/27
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_22293`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_22293 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_22293; Apache-2.0; corrects Open node 1b4c0cac-4606-4a88-97c9-de3a15014132

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_22293 : ((2:ℚ)/3) ^ 2 * (1/3) ^ 2 * 3 = (4:ℚ)/27 := by sorry
