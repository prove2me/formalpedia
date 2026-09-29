-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_45071
-- name    : WorkbookCorrected.plus_45071
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:52:32.242633+00:00
-- url     : https://prove2.me/theorems/73a7d3df-906b-4c2c-9105-7cdd89e267d4
-- title:
--   Binomial-factorial identity #45071
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   3! * (\binom{4}{2}) * (\binom{6}{2}) = 540
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_45071`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_45071 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_45071; Apache-2.0; corrects Open node e9cd02f9-38db-48f6-9379-cfc550cb15d6

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_45071 : (Nat.factorial 3) * (Nat.choose 4 2) * (Nat.choose 6 2) = 540 := by sorry
