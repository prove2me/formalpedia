-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_50116
-- name    : WorkbookCorrected.plus_50116
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-06T20:59:01.034376+00:00
-- url     : https://prove2.me/theorems/e886c844-7ac5-4b8f-8af8-2b5413405f8f
-- title:
--   Elementary arithmetic identity #50116
-- statement:
--   The elementary natural-number identity
--   $$
--   5^5 = 3125
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_50116`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`, and whose stated right-hand side did not match the evaluated left-hand side. The repaired statement keeps the arithmetic left-hand side and uses the evaluated integer right-hand side (original RHS was 625).
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_50116 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_50116; Apache-2.0; corrects Open node e52400d5-1217-4015-b072-a650247aa071

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_50116 : 5 ^ 5 = 3125 := by sorry
