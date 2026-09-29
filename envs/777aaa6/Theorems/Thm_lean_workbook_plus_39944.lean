-- Prove2me | Theorems.Thm_lean_workbook_plus_39944
-- name    : lean_workbook_plus_39944
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/6aceaeeb-df67-47bb-bb39-358654762a26
-- statement:
--   Let $a_1,a_2,...,a_n$ be positive real numbers such that $\sum_{i=1}^{k}a_i \leq \sum_{i=1}^{k}i(i+1), \forall k=1,2,..,n$ . Prove that $\frac{1}{a_1}+\frac{1}{a_2}+...+\frac{1}{a_n} \geq \frac{n}{n+1}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39944 (n : ℕ) (a : ℕ → ℝ) (ha : ∀ k, 0 < a k) (hab : ∀ k, (∑ i in Finset.range k, a i) ≤ (∑ i in Finset.range k, i * (i + 1))) : (∑ i in Finset.range n, (1 / a i)) ≥ n / (n + 1)   :=  by sorry
