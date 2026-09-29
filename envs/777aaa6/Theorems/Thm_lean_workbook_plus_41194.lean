-- Prove2me | Theorems.Thm_lean_workbook_plus_41194
-- name    : lean_workbook_plus_41194
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/cbf57088-a785-40ac-9cb6-635d89acc5c4
-- statement:
--   Calculate the sum of combinations including zero: $\sum_{k=0}^{5}\binom{5}{k}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41194 : ∑ k in Finset.range 6, choose 5 k = 32   :=  by sorry
