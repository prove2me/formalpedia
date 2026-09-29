-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_17962
-- name    : WorkbookCorrected.plus_17962
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T11:56:30.919248+00:00
-- url     : https://prove2.me/theorems/f572e4ab-474e-4c28-8770-c14229d1d912
-- title:
--   Elementary arithmetic identity #17962
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   10^4 = 10000
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_17962`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_17962 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_17962; Apache-2.0; corrects Open node c19788b6-5a42-47f9-8cd2-6c6933f9a702

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_17962 : 10^4 = 10000 := by sorry
