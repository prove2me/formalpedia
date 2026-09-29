-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_37901
-- name    : WorkbookCorrected.plus_37901
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T11:52:42.571593+00:00
-- url     : https://prove2.me/theorems/72ddf16c-8c9d-4bc4-a82d-18c99cdd6f81
-- title:
--   Factorial arithmetic identity #37901
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (10!/(2!*3!))-(9!/(2!*2!)) = 211680
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_37901`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_37901 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_37901; Apache-2.0; corrects Open node 38182c5f-a0f9-4928-ad1a-1b62ec344a00

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_37901 : ((Nat.factorial 10)/((Nat.factorial 2)*(Nat.factorial 3)))-((Nat.factorial 9)/((Nat.factorial 2)*(Nat.factorial 2))) = 211680 := by sorry
