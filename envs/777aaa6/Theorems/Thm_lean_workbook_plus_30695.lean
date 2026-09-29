-- Prove2me | Theorems.Thm_lean_workbook_plus_30695
-- name    : lean_workbook_plus_30695
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/90d5c975-4f80-4c30-9561-8c9e6c14e02f
-- statement:
--   Does it converge? \n\n $\sum_{n=1}^{\infty}e^{-n^2}$ \nWithout integral test
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30695 : ∀ N : ℕ, ∃ M : ℝ, ∀ n : ℕ, n ≥ N → M ≤ ∑ i in Finset.range n, (Real.exp (-i ^ 2))   :=  by sorry
