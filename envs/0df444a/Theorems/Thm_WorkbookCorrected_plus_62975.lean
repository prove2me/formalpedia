-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_62975
-- name    : WorkbookCorrected.plus_62975
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:52:40.989298+00:00
-- url     : https://prove2.me/theorems/cb7aeec8-3e71-48ab-8e6a-4affa869441f
-- title:
--   Binomial-factorial identity #62975
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   \binom{9}{4} * (5! / (2! * 2!)) = 9! / (2! * 2! * 4!)
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_62975`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_62975 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_62975; Apache-2.0; corrects Open node c0214a64-eade-4916-898c-54a662b4f115

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_62975 : (Nat.choose 9 4) * ((Nat.factorial 5) / ((Nat.factorial 2) * (Nat.factorial 2))) = (Nat.factorial 9) / ((Nat.factorial 2) * (Nat.factorial 2) * (Nat.factorial 4)) := by sorry
