-- Prove2me | Theorems.Thm_lean_workbook_plus_43164
-- name    : lean_workbook_plus_43164
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/43bf4ab5-2058-408f-a883-dde0f2a5a213
-- statement:
--   W.Janous's inequality: If $x_{1}+x_{2}+...+x_{n}=1$ where $x_{i}$ are non-negative real numbers and $2\leq k< n$ then $x_{1}x_{2}...x_{k}+x_{2}x_{3}...x_{k+1}+...+x_{n}x_{1}...x_{k-1}\leq max\{\frac{1}{k^{k}},\frac{1}{n^{k-1}}\}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43164 ∀ k n : ℕ, 2 ≤ k ∧ k < n → ∀ x : ℕ → NNReal, ∑ i in Finset.range n, x i = 1 → ∑ i in Finset.range k, ∏ j in Finset.range (i + 1), x (i + j) ≤ max (1 / k ^ k) (1 / n ^ (k - 1))   :=  by sorry
