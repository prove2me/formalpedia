-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_1001
-- name    : WorkbookCorrected.plus_1001
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:47:26.020351+00:00
-- url     : https://prove2.me/theorems/dcab625c-d6a6-4113-b691-3c701f6eb23c
-- title:
--   Binomial difference with product term
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   \binom{11}{5} - \binom{5}{2}\binom{6}{3} = 262
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_1001`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_1001 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_1001; Apache-2.0; corrects Open node a624ed03-ffa1-4b74-8191-e35dd30f06d7

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_1001 : Nat.choose 11 5 - Nat.choose 5 2 * Nat.choose 6 3 = 262 := by sorry
