-- Prove2me | Theorems.Thm_lean_workbook_plus_58794
-- name    : lean_workbook_plus_58794
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/f3b8e74e-641b-4e2d-8dc6-a2b2c2681b16
-- statement:
--   Prove that the partial sums of the series $s_n(x)=\sum_{k=1}^{n}(-1)^{k-1}\cos\left(\frac{x}{n} \right)$ are uniformly bounded on $(-\pi,\pi)$, i.e., show that there exists $M>0$ such that $|s_n(x)|\le M$ for all $x\in(-\pi,\pi)$ and for all $n\ge 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58794 (n : ℕ) : ∃ M, ∀ x ∈ Set.Ioo (-Real.pi) Real.pi, |(∑ k in Finset.range n, (-1)^(k - 1) * Real.cos (x / n))| ≤ M   :=  by sorry
