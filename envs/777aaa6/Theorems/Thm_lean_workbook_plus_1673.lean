-- Prove2me | Theorems.Thm_lean_workbook_plus_1673
-- name    : lean_workbook_plus_1673
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/8f012a93-2447-4f26-9a80-d01b527da8d2
-- statement:
--   Calculate $\sum^{4}_{i=1}2^i$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1673 : ∑ i in Finset.Icc 1 4, 2^i = 30   :=  by sorry
