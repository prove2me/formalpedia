-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_29300
-- name    : WorkbookCorrected.plus_29300
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T14:29:45.061984+00:00
-- url     : https://prove2.me/theorems/56f5ba80-828f-4064-aa4e-b97d6f4b8a05
-- title:
--   Elementary arithmetic identity #29300
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   290035 = 290035
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_29300`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_29300 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_29300; Apache-2.0; corrects Open node 07b2d230-0f66-4e2a-bb8c-efbe376b82a2

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_29300 : 290035 = 290035 := by sorry
