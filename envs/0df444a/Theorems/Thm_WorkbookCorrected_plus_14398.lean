-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_14398
-- name    : WorkbookCorrected.plus_14398
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-22T11:49:26.411686+00:00
-- url     : https://prove2.me/theorems/d04eea29-5008-4ad3-8474-1dd4f12b704c
-- title:
--   Elementary arithmetic identity #14398
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   37^2 + 36^2 = 2665
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_14398`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_14398 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_14398; Apache-2.0; corrects Open node d35b4074-49f9-448b-8a64-95bf688a7c7e

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_14398 : 37^2 + 36^2 = 2665 := by sorry
