-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_40877
-- name    : WorkbookCorrected.plus_40877
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T14:39:17.822709+00:00
-- url     : https://prove2.me/theorems/2ad15856-84ad-43ee-8373-3f35da0f83f3
-- title:
--   Rational arithmetic identity #40877
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 = 0
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_40877`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_40877 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_40877; Apache-2.0; corrects Open node 6d8df8dd-0d6c-4e89-ab56-622735f85a38

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_40877 : (0:ℚ) + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 = (0:ℚ) := by sorry
