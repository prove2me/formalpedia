-- Prove2me | Theorems.Thm_lean_workbook_plus_53314
-- name    : lean_workbook_plus_53314
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/ce0d5834-bf53-4508-8cc3-d18fa2ab0690
-- statement:
--   Prove that $\lim_{n \rightarrow \infty} x_n = 0$ using the infinite product representation $x_n=\prod_{k=1}^n\frac{2k-1}{2k}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53314 (x_n : ℕ → ℝ) (hx_n : ∀ n, x_n = ∏ k in Finset.range n, (2 * k - 1) / (2 * k)) : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |x_n| < ε   :=  by sorry
