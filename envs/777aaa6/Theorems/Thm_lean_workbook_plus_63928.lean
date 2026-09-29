-- Prove2me | Theorems.Thm_lean_workbook_plus_63928
-- name    : lean_workbook_plus_63928
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/1e088a3e-1674-4868-99e4-489aa21ccbc4
-- statement:
--   Evaluate $\displaystyle\sum_{i=0}^{1000}i$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63928 : ∑ i in Finset.range 1001, i = 500500   :=  by sorry
