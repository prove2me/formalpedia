-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_54975
-- name    : WorkbookCorrected.plus_54975
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T08:43:35.507252+00:00
-- url     : https://prove2.me/theorems/771c2819-0524-41f9-b9f4-bce3a5d390b9
-- title:
--   Thousand minus digit-place sum equals 2893
-- statement:
--   The elementary natural-number identity
--   $$
--   1000+(1000-9)+(1000-99)+(1000-999)=2893
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_54975`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_54975 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_54975; Apache-2.0; corrects Open node cc1f4fcf-c616-44ee-98f3-52137ba155db

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_54975 : (1000 : ℕ) + (1000 - 9) + (1000 - 99) + (1000 - 999) = 2893 := by sorry
