-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_53829
-- name    : WorkbookCorrected.plus_53829
-- status  : Disproved
-- author  : @carlok
-- created : 2026-09-30T10:31:35.206044+00:00
-- url     : https://prove2.me/theorems/a642539c-4fd5-437f-a314-51ad19a1f91b
-- title:
--   Factorial arithmetic identity #53829
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   9! / (4! * 2!) = 90
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_53829`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_53829 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_53829; Apache-2.0; corrects Open node ae097b3c-b7d6-4608-be06-0f0ce496be04

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_53829 : (Nat.factorial 9) / ((Nat.factorial 4) * (Nat.factorial 2)) = 90 := by sorry
