-- Prove2me | Theorems.Thm_lean_workbook_plus_79160
-- name    : lean_workbook_plus_79160
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/1730f057-d5e8-4c91-8222-f6d583c5c1ef
-- statement:
--   Let ${x_1,x_2,\cdots,x_n}\in\mathbb{R}$ such that$x_1+x_2+\cdots+x_n=0,$find the smallest $k_n$ such that$k_n(x_1^2+x_2^2+\cdots+x_n^2)\ge{x_1x_2+x_2x_3+\cdots+x_nx_1}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79160 (n : ℕ) : ∃ k_n : ℝ, ∀ x : ℕ → ℝ, ∑ i in Finset.range n, x i = 0 → k_n * ∑ i in Finset.range n, (x i) ^ 2 ≥ ∑ i in Finset.range n, ∑ j in Finset.range n, x i * x j   :=  by sorry
