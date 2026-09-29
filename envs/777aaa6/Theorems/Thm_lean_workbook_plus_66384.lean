-- Prove2me | Theorems.Thm_lean_workbook_plus_66384
-- name    : lean_workbook_plus_66384
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/8e5c93e1-8ef3-4abc-b4b0-7c866e55e977
-- statement:
--   Given $10^5 = 100,000$, find the smallest $n$ where $10^{1/11} \times 10^{2/11} \times ... \times 10^{n/11} > 100,000$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66384 (n : ℕ) : (∏ i in Finset.Icc 1 n, (10:ℝ)^(i/11)) > 100000 → n ≥ 11   :=  by sorry
