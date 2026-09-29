-- Prove2me | Theorems.Thm_lean_workbook_plus_31112
-- name    : lean_workbook_plus_31112
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/49577435-efae-4fe8-818c-66bf2afc6b66
-- statement:
--   Let $n$ be a natural number and $x_{1},x_{2},...,x_{n}$ real numbers. Prove that $\sum_{i=1}^{n}\frac{|x_{i}|}{1+|x_{i}|}\geq \frac{\sum_{i=1}^{n}|x_{i}|}{1+\sum_{i=1}^{n}|x_{i}|}$ with equality iff there is at most one $x_{j}\neq 0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31112 (n : ℕ) (x : ℕ → ℝ) :
  ∑ i in Finset.range n, (|x i| / (1 + |x i|)) ≥ (∑ i in Finset.range n, |x i|) / (1 + ∑ i in Finset.range n, |x i|)
    :=  by sorry
