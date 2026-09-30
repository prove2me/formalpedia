-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_3655
-- name    : WorkbookCorrected.plus_3655
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-30T09:09:15.495428+00:00
-- url     : https://prove2.me/theorems/828995e4-f0ef-411f-98d1-d8c3168f3394
-- title:
--   Elementary inequality #3655
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (\binom{10}{4} < \binom{10}{5}) = True
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_3655`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_3655 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_3655; Apache-2.0; corrects Open node 9c1b5b01-54df-46af-8a07-0ac264faf046

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_3655 : ((Nat.choose 10 4) < (Nat.choose 10 5)) = True := by sorry
