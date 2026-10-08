-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_43736
-- name    : WorkbookCorrected.plus_43736
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-06T20:55:22.877835+00:00
-- url     : https://prove2.me/theorems/d0d33c62-0e79-4c9d-9476-4dfb0c0aed4c
-- title:
--   Binomial coefficient identity #43736
-- statement:
--   The elementary natural-number identity
--   $$
--   (\binom{12}{5}) = 792
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_43736`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`, and whose stated right-hand side did not match the evaluated left-hand side. The repaired statement keeps the combinatorial/arithmetic left-hand side and uses the evaluated integer right-hand side (original RHS was 330).
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_43736 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_43736; Apache-2.0; corrects Open node 866c7d2c-d921-4ad8-94bb-f74717ee815b

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_43736 : ((Nat.choose 12 5)) = 792 := by sorry
