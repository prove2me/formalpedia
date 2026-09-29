-- Prove2me | Theorems.Thm_lean_workbook_plus_69836
-- name    : lean_workbook_plus_69836
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/d568f50d-9c56-4740-8ce0-0f9a9f590582
-- statement:
--   Solve the inequality \(\sum_{i=1}^n x_i(x_i-a)\leq0\) given 0 <= x_i <= a for all i in N^+.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69836 (n : ℕ) (a : ℝ) (x : ℕ → ℝ) (h₁ : ∀ i ∈ Finset.range n, 0 ≤ x i) (h₂ : ∀ i ∈ Finset.range n, x i ≤ a) : ∑ i in Finset.range n, x i * (x i - a) ≤ 0   :=  by sorry
