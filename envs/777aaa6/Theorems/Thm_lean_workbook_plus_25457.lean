-- Prove2me | Theorems.Thm_lean_workbook_plus_25457
-- name    : lean_workbook_plus_25457
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/51440169-5666-4bb7-84d5-2d1b4a724d08
-- statement:
--   Suppose that $f(x)=\sum_{k=1}^{20} x^{d_k}$ . Then $f(x)^2=\sum_{k=1}^{20} x^{2d_k}+2\sum_{1\leq i<j\leq 20} x^{d_i+d_j}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25457  (x : ℝ)
  (d : ℕ → ℕ)
  (h₀ : ∀ k, 1 ≤ k ∧ k ≤ 20)
  (h₁ : f = λ x => ∑ k in Finset.Icc 1 20, x^(d k)) :
  f x^2 = (∑ k in Finset.Icc 1 20, x^(2 * d k)) + 2 * (∑ i in Finset.Icc 1 20, ∑ j in Finset.Icc 1 20, x^(d i + d j))   :=  by sorry
