-- Prove2me | Theorems.Thm_lean_workbook_plus_48411
-- name    : lean_workbook_plus_48411
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/ded3c631-025e-4dd3-b19b-ad811892eda8
-- statement:
--   Why $\frac{\binom{10}0+\binom{10}1+\binom{10}2+\dots+\binom{10}{10}}{2}=\frac{2^{10}}2$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48411 : (∑ i in Finset.range 11, choose 10 i) / 2 = 2^10 / 2   :=  by sorry
