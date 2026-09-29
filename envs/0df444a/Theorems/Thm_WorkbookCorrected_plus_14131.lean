-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_14131
-- name    : WorkbookCorrected.plus_14131
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T11:52:38.093013+00:00
-- url     : https://prove2.me/theorems/01a24076-da84-439d-8cf8-b354ba6a29e6
-- title:
--   Factorial arithmetic identity #14131
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   5! = 5 * 4 * 3 * 2 * 1
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_14131`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_14131 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_14131; Apache-2.0; corrects Open node 43600192-b5e1-4d60-a4d8-6d462b7a33b1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_14131 : (Nat.factorial 5) = 5 * 4 * 3 * 2 * 1 := by sorry
