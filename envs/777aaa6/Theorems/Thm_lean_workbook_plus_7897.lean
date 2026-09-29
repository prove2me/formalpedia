-- Prove2me | Theorems.Thm_lean_workbook_plus_7897
-- name    : lean_workbook_plus_7897
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/6f447709-27cc-4c0d-9e75-7fa497c09c55
-- statement:
--   Find the sum of the first 4 positive integers: $\sum_{x=1}^{4} x$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7897 : ∑ x in Finset.range 4, x + 1 = 10   :=  by sorry
