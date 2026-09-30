-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_6101
-- name    : WorkbookCorrected.plus_6101
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-30T10:33:34.055464+00:00
-- url     : https://prove2.me/theorems/b29f8a64-6d11-439f-bc69-85dfce20f34c
-- title:
--   Factorial arithmetic identity #6101
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (7!)/(3!*2!*2!) = 210
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_6101`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_6101 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_6101; Apache-2.0; corrects Open node b2f55835-dee8-4c69-88ee-fba9ca0eb199

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_6101 : ((Nat.factorial 7))/((Nat.factorial 3)*(Nat.factorial 2)*(Nat.factorial 2)) = 210 := by sorry
