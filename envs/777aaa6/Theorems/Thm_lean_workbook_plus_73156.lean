-- Prove2me | Theorems.Thm_lean_workbook_plus_73156
-- name    : lean_workbook_plus_73156
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/9488952d-5e12-4791-bd56-89663f2984b5
-- statement:
--   Prove $ \left(^n_0\right)+\left(^n_1\right)+\left(^n_2\right)+...+\left(^n_n\right) = 2^n$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73156 : ∀ n, ∑ i in Finset.range (n+1), choose n i = 2^n   :=  by sorry
