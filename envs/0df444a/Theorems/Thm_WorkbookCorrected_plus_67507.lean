-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_67507
-- name    : WorkbookCorrected.plus_67507
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:43:05.359171+00:00
-- url     : https://prove2.me/theorems/72d410cf-0e29-435b-9931-0b0c7c772440
-- title:
--   Thirteen times twelve plus half equals 234
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   13\cdot 12 + \frac{13\cdot 12}{2} = 234
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_67507`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_67507 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_67507; Apache-2.0; corrects Open node 6ca88468-d905-426f-9cdc-8ebf6d3b9897

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_67507 : (13 : ℕ) * 12 + (13 * 12) / 2 = 234 := by sorry
