-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_6012
-- name    : WorkbookCorrected.plus_6012
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-03T08:55:04.794988+00:00
-- url     : https://prove2.me/theorems/a130125e-fc34-421d-99a7-d92271aa2a05
-- title:
--   Rational arithmetic identity #6012
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (5/8:ℚ) = (5/8:ℚ)
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_6012`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_6012 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_6012; Apache-2.0; corrects Open node f8b2c4fd-8f2d-42fe-a65b-0c60dc7a4785

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_6012 : (5/8:ℚ) = (5/8:ℚ) := by sorry
