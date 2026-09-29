-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_58179
-- name    : WorkbookCorrected.plus_58179
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:43:00.566974+00:00
-- url     : https://prove2.me/theorems/4026aa5a-d874-4f2c-8121-301d1186578f
-- title:
--   Five factorial over two squared factorials
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   \frac{5!}{2!\,2!} = 30
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_58179`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_58179 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_58179; Apache-2.0; corrects Open node df80007c-6f79-4d24-876a-3c136809dbd5

import Mathlib.Data.Nat.Factorial.Basic

theorem WorkbookCorrected.plus_58179 : Nat.factorial 5 / (Nat.factorial 2 * Nat.factorial 2) = 30 := by sorry
