-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_4695
-- name    : WorkbookCorrected.plus_4695
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:47:27.970989+00:00
-- url     : https://prove2.me/theorems/2c4dfacc-dfdd-4128-b724-5eab980f0c1f
-- title:
--   Product of squares eight and nine
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   8^2 \cdot 9^2 = 5184
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_4695`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_4695 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_4695; Apache-2.0; corrects Open node 03c55d80-b886-43b5-a1db-817f7af59bbe

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_4695 : (8 : ℕ) ^ 2 * 9 ^ 2 = 5184 := by sorry
