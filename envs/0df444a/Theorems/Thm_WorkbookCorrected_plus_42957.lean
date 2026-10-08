-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_42957
-- name    : WorkbookCorrected.plus_42957
-- status  : Open
-- author  : @carlok
-- created : 2026-10-06T20:55:54.554641+00:00
-- url     : https://prove2.me/theorems/9aa0abf5-be2e-40f9-8753-4a12f1fe909e
-- title:
--   Binomial coefficient identity #42957
-- statement:
--   The elementary natural-number identity
--   $$
--   (\binom{6}{0} - \binom{6}{11}) + (\binom{6}{1} - \binom{6}{7}) + (\binom{6}{2} - \binom{6}{3}) = 2
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_42957`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`, and whose stated right-hand side did not match the evaluated left-hand side. The repaired statement keeps the combinatorial/arithmetic left-hand side and uses the evaluated integer right-hand side (original RHS was 126).
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_42957 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_42957; Apache-2.0; corrects Open node c34da0cb-3709-4e9b-a022-1efc4eb2ead9

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_42957 : ((Nat.choose 6 0) - (Nat.choose 6 11)) + ((Nat.choose 6 1) - (Nat.choose 6 7)) + ((Nat.choose 6 2) - (Nat.choose 6 3)) = 2 := by sorry
