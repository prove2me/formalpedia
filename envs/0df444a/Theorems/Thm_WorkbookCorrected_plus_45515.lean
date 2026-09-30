-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_45515
-- name    : WorkbookCorrected.plus_45515
-- status  : Disproved
-- author  : @carlok
-- created : 2026-09-30T10:31:36.317136+00:00
-- url     : https://prove2.me/theorems/0ceeb2ce-2752-4ad1-990f-b1a196844ed4
-- title:
--   Factorial arithmetic identity #45515
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   10! / (2!^3) = 45000
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_45515`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_45515 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_45515; Apache-2.0; corrects Open node 98b03b61-4abc-42fa-9765-632061114120

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_45515 : (Nat.factorial 10) / ((Nat.factorial 2) ^ 3) = 45000 := by sorry
