-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_41596
-- name    : WorkbookCorrected.plus_41596
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:47:19.183385+00:00
-- url     : https://prove2.me/theorems/0233c30f-bf4d-47e4-9028-e3ed9f94a0a0
-- title:
--   Binomial coefficient C(13,2)
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   \binom{13}{2} = 78
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_41596`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_41596 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_41596; Apache-2.0; corrects Open node e05b1e03-5cc3-4f81-b122-6783c529e094

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_41596 : Nat.choose 13 2 = 78 := by sorry
