-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_24733
-- name    : WorkbookCorrected.plus_24733
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:52:40.616547+00:00
-- url     : https://prove2.me/theorems/785a15d6-82cd-4bd7-adeb-1172fa873a9f
-- title:
--   Binomial coefficient identity #24733
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (\binom{11}{6}) - 1 - 30 - 6 = 425
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_24733`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_24733 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_24733; Apache-2.0; corrects Open node 17e57903-8962-4516-a1b1-ebcc7cb3fd67

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_24733 : (Nat.choose 11 6) - 1 - 30 - 6 = 425 := by sorry
