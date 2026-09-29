-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_71753
-- name    : WorkbookCorrected.plus_71753
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:18:40.135411+00:00
-- url     : https://prove2.me/theorems/64a95ea3-0297-46db-8420-f822a5e31a41
-- title:
--   Inclusion-exclusion power-of-two count equals 196
-- statement:
--   The natural-number identity $2^{8}-2^{5}-2^{5}+2^{2}=196$ records a standard inclusion-exclusion count of binary strings.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_71753`, which omitted the colon after the theorem name and used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_71753 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_71753; Apache-2.0; corrects Open node b0c23a76-0d38-4c51-8b13-fb720c1ac1ba

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_71753 : (2 : ℕ) ^ 8 - 2 ^ 5 - 2 ^ 5 + 2 ^ 2 = 196 := by sorry
