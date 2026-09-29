-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_51332
-- name    : WorkbookCorrected.plus_51332
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-23T13:30:56.98691+00:00
-- url     : https://prove2.me/theorems/0f9ddedf-e451-4e5f-bf82-be7769d1eda8
-- title:
--   Rational arithmetic identity #51332
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (4*(1/2)^4 * 1/2) + (6*(1/2)^4 * 12/16) + (4*(1/2)^4 * 14/16) + ((1/2)^4 * 15/16) = 175/256
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_51332`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_51332 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_51332; Apache-2.0; corrects Open node 6dc9383a-887a-4ad2-8574-7c3a5a4fcc7e

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_51332 : ((4:ℚ)*(1/2) ^ 4 * 1/2) + (6*(1/2) ^ 4 * 12/16) + (4*(1/2) ^ 4 * 14/16) + ((1/2) ^ 4 * 15/16) = (175:ℚ)/256 := by sorry
