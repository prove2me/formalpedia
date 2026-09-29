-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_10983
-- name    : WorkbookCorrected.plus_10983
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T11:49:23.091236+00:00
-- url     : https://prove2.me/theorems/3efac6ba-7280-40bd-9abf-3a63ee400506
-- title:
--   Elementary arithmetic identity #10983
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   5*(9+6+5+3) = 115
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_10983`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_10983 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_10983; Apache-2.0; corrects Open node 52b0c2d0-b3c0-45e6-a222-1b3cec05e03c

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_10983 : 5*(9+6+5+3) = 115 := by sorry
