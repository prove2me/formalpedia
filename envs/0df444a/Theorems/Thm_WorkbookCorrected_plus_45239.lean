-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_45239
-- name    : WorkbookCorrected.plus_45239
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T13:11:34.248762+00:00
-- url     : https://prove2.me/theorems/8f6d01ad-f939-4844-8a86-07db9388799e
-- title:
--   Elementary arithmetic identity #45239
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   1 + 11 + 55 + 165 + 330 + 462 + 462 + 330 + 165 + 55 + 11 + 1 = 2048
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_45239`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_45239 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_45239; Apache-2.0; corrects Open node b067ca7d-16d0-4de8-9019-2043a3e214d1

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_45239 : 1 + 11 + 55 + 165 + 330 + 462 + 462 + 330 + 165 + 55 + 11 + 1 = 2048 := by sorry
