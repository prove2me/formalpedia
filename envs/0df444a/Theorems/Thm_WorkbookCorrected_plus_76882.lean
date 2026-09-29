-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_76882
-- name    : WorkbookCorrected.plus_76882
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:18:28.637588+00:00
-- url     : https://prove2.me/theorems/98a29a6c-c40c-408e-b4ac-1177fe1bc34e
-- title:
--   Three times three times one equals nine
-- statement:
--   The elementary product identity $3\cdot 3\cdot 1=9$ holds in the natural numbers.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_76882`, which omitted the colon after the theorem name and used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_76882 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_76882; Apache-2.0; corrects Open node 52853b18-72ea-4e75-b12b-684c170c1d8e

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_76882 : (3 : ℕ) * 3 * 1 = 9 := by sorry
