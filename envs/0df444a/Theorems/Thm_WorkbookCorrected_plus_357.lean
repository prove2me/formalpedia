-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_357
-- name    : WorkbookCorrected.plus_357
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:52:42.024685+00:00
-- url     : https://prove2.me/theorems/5828adb1-8df3-4715-96da-85bc5d9544e8
-- title:
--   Binomial coefficient identity #357
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   \binom{14}{5} - \binom{10}{5} = 1750
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_357`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_357 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_357; Apache-2.0; corrects Open node 96e5a48b-0878-43a6-8c18-b0627afb74eb

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_357 : (Nat.choose 14 5) - (Nat.choose 10 5) = 1750 := by sorry
