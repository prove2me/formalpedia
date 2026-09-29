-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_35148
-- name    : WorkbookCorrected.plus_35148
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:52:43.103214+00:00
-- url     : https://prove2.me/theorems/09a28388-c4d3-488a-bb1c-8d91cabcc673
-- title:
--   Binomial coefficient identity #35148
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (\binom{10}{4}) - (\binom{6}{4} + \binom{4}{1} * \binom{6}{3}) = 115
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_35148`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_35148 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_35148; Apache-2.0; corrects Open node c094b4b9-d4e6-46c9-b0c3-9232d164808d

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_35148 : (Nat.choose 10 4) - ((Nat.choose 6 4) + (Nat.choose 4 1) * (Nat.choose 6 3)) = 115 := by sorry
