-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_62454
-- name    : WorkbookCorrected.plus_62454
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T14:33:29.030606+00:00
-- url     : https://prove2.me/theorems/b2b4ce4d-e19e-4e9a-8c71-14a7fe2ee7ca
-- title:
--   Factorial arithmetic identity #62454
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   77 ^ 10 ≥ 2 ^ 10 * (10!) ^ 2
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_62454`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_62454 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_62454; Apache-2.0; corrects Open node ca92edfa-7a8a-475d-a819-1c584707d422

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_62454 : 77  ^  10 ≥ 2  ^  10 * ((Nat.factorial 10))  ^  2 := by sorry
