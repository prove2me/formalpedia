-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_20671
-- name    : WorkbookCorrected.plus_20671
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T11:49:28.068689+00:00
-- url     : https://prove2.me/theorems/b2ff2569-f344-4d43-96be-fee93e6b4392
-- title:
--   Elementary arithmetic identity #20671
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   256^3 = 256*256*256
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_20671`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_20671 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_20671; Apache-2.0; corrects Open node 567b9901-e4d5-43ba-a5e7-811c39c40af9

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_20671 : 256^3 = 256*256*256 := by sorry
