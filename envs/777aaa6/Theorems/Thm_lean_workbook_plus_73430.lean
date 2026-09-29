-- Prove2me | Theorems.Thm_lean_workbook_plus_73430
-- name    : lean_workbook_plus_73430
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/9c6c6173-cdf5-409b-a9b2-da3257d3a3a7
-- statement:
--   we have $1+\sum_{k=1}^{657}{2\over (3k-1)(3k)(3k+1)} = 1+\sum_{k=1}^{657}\left({1\over 3k-1}-{2\over 3k}+{1\over 3k+1}\right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73430 : (1 + ∑ k in Finset.Icc 1 657, (2 / ((3 * k - 1) * (3 * k) * (3 * k + 1)))) = (1 + ∑ k in Finset.Icc 1 657, (1 / (3 * k - 1) - 2 / (3 * k) + 1 / (3 * k + 1)))   :=  by sorry
