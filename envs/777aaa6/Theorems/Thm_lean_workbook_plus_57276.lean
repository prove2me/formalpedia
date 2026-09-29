-- Prove2me | Theorems.Thm_lean_workbook_plus_57276
-- name    : lean_workbook_plus_57276
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/7d5cc1ba-89d5-4ab3-b447-a89d7875c094
-- statement:
--   We have the sum of the integers from 1 to 1000, which is just $\frac{(1000)(1001)}{2}$ , or 500500.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57276 :
  ∑ k in (Finset.range 1000), k = 500500   :=  by sorry
