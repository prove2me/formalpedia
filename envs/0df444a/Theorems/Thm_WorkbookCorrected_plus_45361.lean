-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_45361
-- name    : WorkbookCorrected.plus_45361
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-01T06:55:22.617406+00:00
-- url     : https://prove2.me/theorems/2e1f1f50-3d08-4fab-9ffe-8d2d5dfa8f9e
-- title:
--   Factorial arithmetic identity #45361
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (factorial 15)/(factorial 9 * factorial 6) = 5005
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_45361`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_45361 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_45361; Apache-2.0; corrects Open node e34087f4-9e4f-4aea-982a-20cb64ca060c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_45361 : ((Nat.factorial 15))/((Nat.factorial 9) * (Nat.factorial 6)) = 5005 := by sorry
