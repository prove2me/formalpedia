-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_57098
-- name    : WorkbookCorrected.plus_57098
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:28:45.014394+00:00
-- url     : https://prove2.me/theorems/b56457ff-1807-4724-ba99-5ab024ceeee5
-- title:
--   Binomial coefficient C(6,2) equals 15
-- statement:
--   The elementary natural-number identity
--   $$
--   \binom{6}{2}=15
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_57098`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_57098 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_57098; Apache-2.0; corrects Open node c1e9bfb7-f464-4ac4-a35a-da15a3b3ad5c

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_57098 : Nat.choose 6 2 = 15 := by sorry
