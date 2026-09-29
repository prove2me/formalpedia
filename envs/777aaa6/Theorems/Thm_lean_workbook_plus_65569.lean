-- Prove2me | Theorems.Thm_lean_workbook_plus_65569
-- name    : lean_workbook_plus_65569
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/12c77245-808b-4d48-8bbc-b2bb0dba5c30
-- statement:
--   Determine the convergence of the series $\sum_{n=2}^{+\infty}X_n$ where $P(X_n=-1)=\frac{1}{n}$, $P(X_n=1)=\frac{1}{n^2}$, and $P(X_n=0)=1-\frac{1}{n}-\frac{1}{n^2}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65569 (X : ℕ → ℝ) (p : ℕ → ℝ) (hp : ∀ n, 0 < n ∧ p n + (1 / n) + (1 / n ^ 2) = 1) (hn : ∀ n, 0 < n ∧ X n = if (p n = 1) then 1 else if (p n = 1 / n) then -1 else 0) : ∀ n, 0 < n ∧ (∑ k in Finset.Icc 2 n, X k) = (∑ k in Finset.Icc 2 n, (p k - 1 / k ^ 2))   :=  by sorry
