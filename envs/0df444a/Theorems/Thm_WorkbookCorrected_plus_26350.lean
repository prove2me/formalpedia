-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_26350
-- name    : WorkbookCorrected.plus_26350
-- status  : Disproved
-- author  : @carlok
-- created : 2026-09-23T13:26:09.727656+00:00
-- url     : https://prove2.me/theorems/e630df2b-d8fa-4f9e-9dcc-91753f41aac6
-- title:
--   Binomial coefficient identity #26350
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (\binom{50}{6}) - (\binom{5}{1} * \binom{40}{6}) + (\binom{5}{2} * \binom{30}{6}) - (\binom{5}{3} * \binom{20}{6}) + (\binom{5}{4} * \binom{10}{6}) = 2250000
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_26350`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_26350 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_26350; Apache-2.0; corrects Open node 5b270a60-54b7-4117-9b68-abaacd95c490

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_26350 : ((Nat.choose 50 6)) - ((Nat.choose 5 1) * (Nat.choose 40 6)) + ((Nat.choose 5 2) * (Nat.choose 30 6)) - ((Nat.choose 5 3) * (Nat.choose 20 6)) + ((Nat.choose 5 4) * (Nat.choose 10 6)) = 2250000 := by sorry
