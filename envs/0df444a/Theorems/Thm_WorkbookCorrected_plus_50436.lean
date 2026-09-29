-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_50436
-- name    : WorkbookCorrected.plus_50436
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-23T13:08:36.710728+00:00
-- url     : https://prove2.me/theorems/26b46286-f2d5-477b-8940-8ffedb6c428b
-- title:
--   Binomial coefficient identity #50436
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (\binom{8}{2} * 16) = 448
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_50436`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_50436 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_50436; Apache-2.0; corrects Open node f3980ae4-97e3-4fb3-9eee-200a4efe5440

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_50436 : ((Nat.choose 8 2) * 16) = 448 := by sorry
