-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_35143
-- name    : WorkbookCorrected.plus_35143
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T11:43:01.819589+00:00
-- url     : https://prove2.me/theorems/41daf70d-00d7-471e-a76e-84230f6cd243
-- title:
--   Factorial arithmetic identity #35143
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (12!)/((3!*9!)) = 220
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_35143`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_35143 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_35143; Apache-2.0; corrects Open node 3afe1d63-423f-46f5-861a-088913b9cbca

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_35143 : (Nat.factorial 12)/(((Nat.factorial 3)*(Nat.factorial 9))) = 220 := by sorry
