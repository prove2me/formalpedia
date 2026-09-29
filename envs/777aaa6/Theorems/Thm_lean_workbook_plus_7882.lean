-- Prove2me | Theorems.Thm_lean_workbook_plus_7882
-- name    : lean_workbook_plus_7882
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/4f8ea27f-54a7-4324-abeb-5f730cbae2dc
-- statement:
--   Find the sum of the series: $\sum_{k=1}^{100}\left[(k^2-k)+\frac{1}{k}-\frac{1}{(k+2)}\right]$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7882 (k : ℕ) : ∑ k in Finset.Icc 1 100, ((k^2 - k) + 1/k - 1/(k + 2)) = 330003   :=  by sorry
