-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_19389
-- name    : WorkbookCorrected.plus_19389
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-06T20:59:15.656196+00:00
-- url     : https://prove2.me/theorems/1906d456-81d9-4c39-b084-e269e2c702df
-- title:
--   Elementary arithmetic identity #19389
-- statement:
--   The elementary natural-number identity
--   $$
--   1 + 20 + 400 + 8000 + 160000 = 168421
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_19389`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`, and whose stated right-hand side did not match the evaluated left-hand side. The repaired statement keeps the arithmetic left-hand side and uses the evaluated integer right-hand side (original RHS was 168081).
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_19389 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_19389; Apache-2.0; corrects Open node 56be0635-b0c9-4e3f-8cad-17142cc89ad6

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_19389 : 1 + 20 + 400 + 8000 + 160000 = 168421 := by sorry
