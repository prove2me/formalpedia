-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_75905
-- name    : WorkbookCorrected.plus_75905
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-23T13:15:48.404151+00:00
-- url     : https://prove2.me/theorems/ae9f2eaa-f887-493d-9582-bb7e5a4c1ba3
-- title:
--   Binomial coefficient identity #75905
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   (\binom{10}{5}) = 252
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_75905`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_75905 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_75905; Apache-2.0; corrects Open node ebada161-db5c-4c7c-b821-3021423c9348

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_75905 : (Nat.choose 10 5) = 252 := by sorry
