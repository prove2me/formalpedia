-- Prove2me | Theorems.Thm_lean_workbook_plus_13069
-- name    : lean_workbook_plus_13069
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/34168639-9e44-4319-9562-c2ff00eb1df7
-- statement:
--   Compute $1 + 3 + 3^2 + . . . + 3^{100}$ (in terms of an exponent)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13069 : ∑ i in Finset.range 101, 3^i = 3^101 - 1   :=  by sorry
