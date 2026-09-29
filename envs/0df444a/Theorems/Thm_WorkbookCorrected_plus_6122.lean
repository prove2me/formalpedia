-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_6122
-- name    : WorkbookCorrected.plus_6122
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:47:24.256629+00:00
-- url     : https://prove2.me/theorems/79fd29ab-0bbd-4e60-aced-2268e3cea866
-- title:
--   Difference of binomial coefficients
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   \binom{16}{4} - \binom{14}{4} = 819
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_6122`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_6122 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_6122; Apache-2.0; corrects Open node 9f7aef63-d93f-4cf1-a07f-b574acebd9dd

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_6122 : Nat.choose 16 4 - Nat.choose 14 4 = 819 := by sorry
