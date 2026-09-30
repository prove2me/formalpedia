-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_20500
-- name    : WorkbookCorrected.plus_20500
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-30T07:00:24.986188+00:00
-- url     : https://prove2.me/theorems/288262ca-77a5-4c1f-ac6b-e48ba7b47cb4
-- title:
--   Rational arithmetic identity #20500
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (29/45:ℚ) = (29/45:ℚ)
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_20500`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_20500 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_20500; Apache-2.0; corrects Open node 31ab12e2-d220-45fc-a14a-fadea91a45b3

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_20500 : (29/45:ℚ) = (29/45:ℚ) := by sorry
