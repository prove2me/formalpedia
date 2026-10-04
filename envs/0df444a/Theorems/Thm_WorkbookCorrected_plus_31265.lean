-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_31265
-- name    : WorkbookCorrected.plus_31265
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-03T08:36:51.730572+00:00
-- url     : https://prove2.me/theorems/fbb3a08f-d55f-4846-a64d-06dbc92be13d
-- title:
--   Rational arithmetic identity #31265
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (81/1000:ℚ) = (81/1000:ℚ)
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_31265`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_31265 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_31265; Apache-2.0; corrects Open node 730f3d03-0cf0-4061-9846-d8c4592d1acc

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_31265 : (81/1000:ℚ) = (81/1000:ℚ) := by sorry
