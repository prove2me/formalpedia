-- Prove2me | Theorems.Thm_lean_workbook_plus_37641
-- name    : lean_workbook_plus_37641
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/bd2c58b2-b951-4ce0-9b22-024e59ee751f
-- statement:
--   $ \sum_{i = 1}^{n} (x_i - y_i)^2 \leq \sum_{i = 1}^{n} (x_i - z_i)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37641 (n : ℕ) (x y z : ℕ → ℝ) (h₁ : n > 0) (h₂ : ∀ i, 1 ≤ i ∧ i ≤ n → (x i - y i) ^ 2 ≤ (x i - z i) ^ 2) : ∑ i in Finset.Icc 1 n, (x i - y i) ^ 2 ≤ ∑ i in Finset.Icc 1 n, (x i - z i) ^ 2   :=  by sorry
