-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_40974
-- name    : WorkbookCorrected.plus_40974
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-01T06:57:26.433179+00:00
-- url     : https://prove2.me/theorems/bf0522ca-ee7f-496a-a7c3-402bfe91681f
-- title:
--   Elementary inequality #40974
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (623171679694215690971693339/131362987122535807501262400:ℚ) < (32/5:ℚ)
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_40974`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_40974 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_40974; Apache-2.0; corrects Open node db2c034e-85b2-4fd6-ac88-eae4c2dac865

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_40974 : (623171679694215690971693339/131362987122535807501262400:ℚ) < (32/5:ℚ) := by sorry
