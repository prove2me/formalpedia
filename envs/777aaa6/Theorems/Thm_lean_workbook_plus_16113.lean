-- Prove2me | Theorems.Thm_lean_workbook_plus_16113
-- name    : lean_workbook_plus_16113
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/b4b8f0a2-2c71-4801-990d-6ad3c32b8516
-- statement:
--   The $i^{th}$ number $(i=2,3, . . . ,n)$ will get swapped if and only if it is the smallest of the first $i$ elements. The probability of this happening is $1/i$. Hence the average number of swaps is just $\frac{1}{2} + \frac{1}{3} + ... + \frac{1}{n} = H_n - 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16113  (n : ℕ)
  (h₀ : 0 < n) :
  (∑ k in Finset.Icc 2 n, (1 : ℝ)/k) = (∑ k in Finset.Icc 2 n, (1 : ℝ)/k)   :=  by sorry
