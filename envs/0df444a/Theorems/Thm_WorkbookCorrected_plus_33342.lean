-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_33342
-- name    : WorkbookCorrected.plus_33342
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:52:37.013993+00:00
-- url     : https://prove2.me/theorems/11f94eab-c8f0-41e4-8a23-488bba0fb0d2
-- title:
--   Binomial coefficient identity #33342
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (\binom{12}{3})/2 = 110
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_33342`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_33342 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_33342; Apache-2.0; corrects Open node 91b602fe-4286-4a68-890b-c6d7b91c7dc0

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_33342 : (Nat.choose 12 3) / 2 = 110 := by sorry
