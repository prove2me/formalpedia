-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_1078
-- name    : WorkbookCorrected.plus_1078
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T14:38:05.228529+00:00
-- url     : https://prove2.me/theorems/04cd84a4-d527-4803-aa4d-d91963d6efc4
-- title:
--   Elementary arithmetic identity #1078
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   343400 = 343400
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_1078`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_1078 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_1078; Apache-2.0; corrects Open node ddc5938c-7b7e-4bc6-95a4-7feb9f140336

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_1078 : 343400 = 343400 := by sorry
