-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_26043
-- name    : WorkbookCorrected.plus_26043
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T19:08:00.256617+00:00
-- url     : https://prove2.me/theorems/83db37b0-2d45-4606-8dca-25a10880b2ac
-- title:
--   Binomial coefficient identity #26043
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (Nat.choose (15-1) (3-1)) = 91
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_26043`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_26043 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_26043; Apache-2.0; corrects Open node b4e3ce86-50a9-4067-8164-6cef942543ab

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_26043 : (Nat.choose (15-1) (3-1)) = 91 := by sorry
