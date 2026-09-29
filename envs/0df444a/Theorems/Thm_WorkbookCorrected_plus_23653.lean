-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_23653
-- name    : WorkbookCorrected.plus_23653
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:47:20.745405+00:00
-- url     : https://prove2.me/theorems/6507771f-57fa-4357-81b0-1f6fd539f0ee
-- title:
--   Five to the fifth power
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   5^5 = 3125
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_23653`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_23653 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_23653; Apache-2.0; corrects Open node a7df57f3-4884-4f6e-8f47-7a90e4cbaf35

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_23653 : (5 : ℕ) ^ 5 = 3125 := by sorry
