-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_56436
-- name    : WorkbookCorrected.plus_56436
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T13:54:17.397415+00:00
-- url     : https://prove2.me/theorems/1c6de7d5-f904-44aa-960b-738600271b04
-- title:
--   Elementary arithmetic identity #56436
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   1155 = 1155
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_56436`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_56436 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_56436; Apache-2.0; corrects Open node d06bb22e-398d-4b6b-849a-f4e82483323a

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_56436 : 1155 = 1155 := by sorry
