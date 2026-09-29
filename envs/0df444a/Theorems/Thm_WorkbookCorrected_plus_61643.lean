-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_61643
-- name    : WorkbookCorrected.plus_61643
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:28:49.28825+00:00
-- url     : https://prove2.me/theorems/0c38e896-b9a4-4bc7-93ac-40331d01d10d
-- title:
--   Weighted sum equals 760
-- statement:
--   The elementary natural-number identity
--   $$
--   52\cdot 5 + 4\cdot 73 + 8\cdot 26 = 760
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_61643`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_61643 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_61643; Apache-2.0; corrects Open node 4a08bf9d-81eb-48cd-ada1-5cb4f9aeed8a

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_61643 : (52 : ℕ) * 5 + 4 * 73 + 8 * 26 = 760 := by sorry
