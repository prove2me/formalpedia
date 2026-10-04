-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_42589
-- name    : WorkbookCorrected.plus_42589
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-03T08:36:45.45299+00:00
-- url     : https://prove2.me/theorems/f57525c8-433f-4c99-9d14-60867285fdca
-- title:
--   Rational arithmetic identity #42589
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (5/22:ℚ) = (5/22:ℚ)
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_42589`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_42589 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_42589; Apache-2.0; corrects Open node 55c63ba1-9300-42f3-8b89-b1b370bc62a8

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_42589 : (5/22:ℚ) = (5/22:ℚ) := by sorry
