-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_1673
-- name    : WorkbookCorrected.plus_1673
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T12:48:31.669315+00:00
-- url     : https://prove2.me/theorems/83b78afc-d0f6-464e-842f-0cbddc384c12
-- title:
--   Elementary arithmetic identity #1673
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   2 + 4 + 8 + 16 = 30
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_1673`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_1673 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_1673; Apache-2.0; corrects Open node 8f012a93-2447-4f26-9a80-d01b527da8d2

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_1673 : 2 + 4 + 8 + 16 = 30 := by sorry
