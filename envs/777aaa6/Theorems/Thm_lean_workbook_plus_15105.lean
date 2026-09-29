-- Prove2me | Theorems.Thm_lean_workbook_plus_15105
-- name    : lean_workbook_plus_15105
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/eb6e8514-5d92-49ea-8578-a45305055ca5
-- statement:
--   We consider two sequences of real numbers $x_{1} \geq x_{2} \geq \ldots \geq x_{n}$ and $\ y_{1} \geq y_{2} \geq \ldots \geq y_{n}.$ Let $z_{1}, z_{2}, .\ldots, z_{n}$ be a permutation of the numbers $y_{1}, y_{2}, \ldots, y_{n}.$ Prove that $\sum \limits_{i=1}^{n} ( x_{i} -\ y_{i} )^{2} \leq \sum \limits_{i=1}^{n} ( x_{i} - z_{i})^{2}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15105 {n : ℕ} (x y : ℕ → ℝ) (z : ℕ → ℝ) (hx : ∀ i, x i ≥ x (i + 1)) (hy : ∀ i, y i ≥ y (i + 1)) (hz : ∀ i, z i ≥ z (i + 1)) (hxy : ∀ i, y i ≥ x i) (hyz : ∀ i, z i ≥ y i) : (∑ i in Finset.range n, (x i - y i) ^ 2) ≤ (∑ i in Finset.range n, (x i - z i) ^ 2)   :=  by sorry
