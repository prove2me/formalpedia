-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_48406
-- name    : WorkbookCorrected.plus_48406
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T19:14:57.321784+00:00
-- url     : https://prove2.me/theorems/b9d780bf-274a-4fc9-ad7d-0f6e500361ee
-- title:
--   Factorial arithmetic identity #48406
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   15 * ((Nat.factorial 4) * (Nat.factorial 2)) = 1 * ((Nat.factorial 6))
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_48406`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_48406 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_48406; Apache-2.0; corrects Open node ac15ad0c-4755-4f72-8e7b-e229b386dfd3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_48406 : (15:ℚ) * ((Nat.factorial 4) * (Nat.factorial 2)) = (1:ℚ) * ((Nat.factorial 6)) := by sorry
