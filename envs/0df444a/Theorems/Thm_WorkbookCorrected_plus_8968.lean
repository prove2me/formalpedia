-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_8968
-- name    : WorkbookCorrected.plus_8968
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:47:29.3156+00:00
-- url     : https://prove2.me/theorems/d83c7e37-200f-4657-b740-baef58e2330c
-- title:
--   Partial sum of binomial coefficients
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   \binom{3}{0}+\binom{4}{1}+\binom{5}{2}=\binom{6}{2}
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_8968`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_8968 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_8968; Apache-2.0; corrects Open node aff26194-f2bc-4d1c-980c-fca599f3bcc2

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_8968 : Nat.choose 3 0 + Nat.choose 4 1 + Nat.choose 5 2 = Nat.choose 6 2 := by sorry
