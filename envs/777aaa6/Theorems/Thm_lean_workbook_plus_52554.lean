-- Prove2me | Theorems.Thm_lean_workbook_plus_52554
-- name    : lean_workbook_plus_52554
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/64028351-b0ff-4cfd-a4e5-722f77f781fe
-- statement:
--   Prove the inequality: $7\left(\sum_{i=1}^n h_i^2\right)^2 - 4\sum_{i=1}^n h_i^3 \geq 0$ where $\sum_{i=1}^n h_i = 1$ and $h_i \geq 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52554 (n : ℕ) (h : ℕ → NNReal) (h_sum : ∑ i in Finset.range n, h i = 1) : 7 * (∑ i in Finset.range n, h i ^ 2) ^ 2 - 4 * ∑ i in Finset.range n, h i ^ 3 ≥ 0   :=  by sorry
