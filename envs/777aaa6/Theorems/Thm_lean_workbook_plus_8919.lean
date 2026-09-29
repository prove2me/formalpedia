-- Prove2me | Theorems.Thm_lean_workbook_plus_8919
-- name    : lean_workbook_plus_8919
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/7c39b4af-900c-4dcc-b555-e712cc9aca9e
-- statement:
--   Calculate the sum of squares from 1 to 4: $\sum_{n=1}^{4} n^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8919 : ∑ n in Finset.Icc 1 4, n^2 = 30   :=  by sorry
