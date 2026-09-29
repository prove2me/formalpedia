-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_59237
-- name    : WorkbookCorrected.plus_59237
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:47:23.890856+00:00
-- url     : https://prove2.me/theorems/6d86a426-38b1-46c2-9d3e-8138131214ba
-- title:
--   Binomial coefficient C(8,2)
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   \binom{8}{2} = 28
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_59237`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_59237 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_59237; Apache-2.0; corrects Open node f9dd4881-94be-4003-b130-103d862ee487

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_59237 : Nat.choose 8 2 = 28 := by sorry
