-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_78077
-- name    : WorkbookCorrected.plus_78077
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:18:36.933619+00:00
-- url     : https://prove2.me/theorems/319a028b-95c3-4a45-9634-4e6d9b752bae
-- title:
--   Weighted sum six plus ten plus fifteen plus twenty-one
-- statement:
--   The natural-number weighted sum $6\cdot 1+10\cdot 1+15\cdot 1+7\cdot 3$ equals $52$.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_78077`, which omitted the colon after the theorem name and used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_78077 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_78077; Apache-2.0; corrects Open node 88bea0a6-2ceb-4c8f-9cda-c150c10f7a52

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_78077 : (6 : ℕ) * 1 + 10 * 1 + 15 * 1 + 7 * 3 = 52 := by sorry
