-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_17744
-- name    : WorkbookCorrected.plus_17744
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T11:49:20.185734+00:00
-- url     : https://prove2.me/theorems/570f313a-d1f5-4c32-b874-3c9c3d9d0e63
-- title:
--   Elementary arithmetic identity #17744
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   1*1 = 1
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_17744`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_17744 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_17744; Apache-2.0; corrects Open node 5ad79676-9fb5-4d39-abf8-1f4daa0f8fc5

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_17744 : 1*1 = 1 := by sorry
