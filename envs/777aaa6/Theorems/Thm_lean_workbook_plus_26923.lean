-- Prove2me | Theorems.Thm_lean_workbook_plus_26923
-- name    : lean_workbook_plus_26923
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/31b72335-0040-46ea-bc29-6da46d4df108
-- statement:
--   Given $x_n \leq M$ for all $n$, prove that the sequence $s_N = \sum_{n=1}^N \sqrt{x_n}$ is bounded and increasing.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26923  (x : ℕ → ℝ)
  (M : ℝ)
  (N : ℕ)
  (h₁ : ∀ n, x n ≤ M)
  : ∃ B, ∀ n ≤ N, (∑ k in Finset.range n, Real.sqrt (x k)) ≤ B   :=  by sorry
