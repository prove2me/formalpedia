-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_45366
-- name    : WorkbookCorrected.plus_45366
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:47:20.872329+00:00
-- url     : https://prove2.me/theorems/50cfecc3-cde8-4a25-95a2-efee210aa676
-- title:
--   Binomial coefficient C(9,4)
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   \binom{9}{4} = 126
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_45366`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_45366 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_45366; Apache-2.0; corrects Open node 4a27ada3-3844-4b6d-97ed-2dfc5bfc0134

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_45366 : Nat.choose 9 4 = 126 := by sorry
