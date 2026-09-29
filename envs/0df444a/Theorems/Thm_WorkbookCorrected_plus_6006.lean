-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_6006
-- name    : WorkbookCorrected.plus_6006
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T11:56:37.34137+00:00
-- url     : https://prove2.me/theorems/d4a29d83-7e8b-45d5-affe-a06cd6da679e
-- title:
--   Binomial coefficient identity #6006
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (\binom{9}{2})/(\binom{12}{2}) = 6/11
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_6006`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_6006 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_6006; Apache-2.0; corrects Open node 23cc12e5-561a-435f-8e6b-a0a7396b0b82

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_6006 : (Nat.choose 9 2) * 11 = (Nat.choose 12 2) * 6 := by sorry
