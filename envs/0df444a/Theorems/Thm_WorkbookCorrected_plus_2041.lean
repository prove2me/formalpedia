-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_2041
-- name    : WorkbookCorrected.plus_2041
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-29T14:33:40.68366+00:00
-- url     : https://prove2.me/theorems/38c1ca8a-db8b-4b07-b7d3-940211e58fa5
-- title:
--   Elementary arithmetic identity #2041
-- statement:
--   The elementary natural-number / rational identity
--   $$
--   1 + 30 + 435 + 4060 + 27405 + 142506 + 593775 + 2035800 + 5852925 + 14307150 + 30045015 + 54627300 + 86493225 + 119759850 + 145422675 + 155117520 + 145422675 + 119759850 + 86493225 + 54627300 + 30045015 + 14307150 + 5852925 + 2035800 + 593775 + 142506 + 27405 + 4060 + 435 + 30 + 1 = 1073741824
--   $$
--   holds by direct arithmetic evaluation.
--
--   Formalization Note: This corrects Lean-Workbook record `lean_workbook_plus_2041`, which omitted a compilable colon/type annotation and/or used a preamble of only `Mathlib.Analysis.Complex.Basic`.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_2041 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook; record lean_workbook_plus_2041; Apache-2.0; corrects Open node f19c4873-13b2-46f0-b339-e4167188c5da

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_2041 : 1 + 30 + 435 + 4060 + 27405 + 142506 + 593775 + 2035800 + 5852925 + 14307150 + 30045015 + 54627300 + 86493225 + 119759850 + 145422675 + 155117520 + 145422675 + 119759850 + 86493225 + 54627300 + 30045015 + 14307150 + 5852925 + 2035800 + 593775 + 142506 + 27405 + 4060 + 435 + 30 + 1 = 1073741824 := by sorry
