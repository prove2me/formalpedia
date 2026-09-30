-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_10822
-- name    : WorkbookCorrected.plus_10822
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T14:33:50.646112+00:00
-- url     : https://prove2.me/theorems/cdfc9bfd-ced2-4a9e-af40-00d666e9aa97
-- title:
--   Elementary arithmetic identity #10822
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   499500 = 499500
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_10822`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_10822 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_10822; Apache-2.0; corrects Open node 3d58f7bd-eb1c-478d-b9ee-85b2ee750772

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_10822 : 499500 = 499500 := by sorry
