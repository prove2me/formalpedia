-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_76719
-- name    : WorkbookCorrected.plus_76719
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:24:56.497569+00:00
-- url     : https://prove2.me/theorems/7350d185-2306-4eaa-acb7-04565d66e6d7
-- title:
--   Difference of two binomial coefficients
-- statement:
--   The binomial difference identity
--   $$
--   \binom{18}{4}-\binom{10}{3}=2940
--   $$
--   holds in the natural numbers.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_76719`, which used a preamble of only `Mathlib.Analysis.Complex.Basic` (and, where relevant, non-compiling notation such as bare `φ`).
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_76719 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_76719; Apache-2.0; corrects Open node de7ac69d-fbb1-4fbb-8bd9-d0c4c80de4c6

import Mathlib.Data.Nat.Choose.Basic

theorem WorkbookCorrected.plus_76719 : Nat.choose 18 4 - Nat.choose 10 3 = 2940 := by sorry
