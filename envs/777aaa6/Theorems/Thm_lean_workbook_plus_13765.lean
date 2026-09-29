-- Prove2me | Theorems.Thm_lean_workbook_plus_13765
-- name    : lean_workbook_plus_13765
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/d77497e0-17c2-4d6a-a28a-d5bcf8ed4adf
-- statement:
--   Prove the Fuchs inequality: Let $ f$ be a convex function. $p_{1},p_{2},...,p_{n}$ are positive. If $x_{1}\geq{x_{2}}\geq...\geq{x_{n}}$ and $y_{1}\geq{y_{2}}\geq...\geq{y_{n}}$ such that $\sum_{i=1}^{k}{p_{i}x_{i}}\geq\sum_{i=1}^{k}{p_{i}y_{i}} (1\leqq\leq{n-1}) $ and $\sum_{i=1}^{n}{p_{i}x_{i}}=\sum_{i=1}^{nk}{p_{i}y_{i}}$, then $\sum_{i=1}^{n}{p_{i}f(x_{i})}\geq\sum_{i=1}^{n}{p_{i}f(y_{i})}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13765 (n : ℕ) (p : ℕ → ℝ) (x y : ℕ → ℝ) (f : ℝ → ℝ) (hp : ∀ i, 0 < p i) (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) (hxy : ∀ i, x i ≥ x (i + 1)) (hyx : ∀ i, y i ≥ y (i + 1)) (h : ∑ i in Finset.range n, p i * x i = ∑ i in Finset.range n, p i * y i) (hf : ∀ i j, i ≤ j → f (x i) + (j - i) * (f (x j) - f (x i)) / (j - i) ≥ f (y i) + (j - i) * (f (y j) - f (y i)) / (j - i)) : ∑ i in Finset.range n, p i * f (x i) ≥ ∑ i in Finset.range n, p i * f (y i)   :=  by sorry
