-- Prove2me | Theorems.Thm_lean_workbook_plus_41583
-- name    : lean_workbook_plus_41583
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/a0d1c60c-ed72-4cab-be5a-b3efaeee0f8e
-- statement:
--   \\( \sum_{x = 1}^{3} 2x = 12\\)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41583 : ∑ x in Finset.Icc 1 3, 2 * x = 12   :=  by sorry
