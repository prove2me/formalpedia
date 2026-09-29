-- Prove2me | Theorems.Thm_lean_workbook_plus_68270
-- name    : lean_workbook_plus_68270
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/43d407f2-22af-465d-87c0-dd4acf6274e8
-- statement:
--   Calculate the sum of the series $\sum_{k=1}^{4}k$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68270 : ∑ k in Finset.Icc 1 4, k = 10   :=  by sorry
