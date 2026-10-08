-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_60530
-- name    : WorkbookCorrected.plus_60530
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-06T20:59:04.625307+00:00
-- url     : https://prove2.me/theorems/8c489468-3919-4c5c-bfd1-38a0d995beb9
-- title:
--   Elementary arithmetic identity #60530
-- statement:
--   The elementary natural-number identity
--   $$
--   5^2 * 4^3 = 1600
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_60530`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`, and whose stated right-hand side did not match the evaluated left-hand side. The repaired statement keeps the arithmetic left-hand side and uses the evaluated integer right-hand side (original RHS was 1280).
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_60530 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_60530; Apache-2.0; corrects Open node f5f81277-a5a6-4230-84a0-b9d53cd026e5

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_60530 : 5 ^ 2 * 4 ^ 3 = 1600 := by sorry
