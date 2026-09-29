-- Prove2me | Theorems.Thm_lean_workbook_plus_32667
-- name    : lean_workbook_plus_32667
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/7a09bb2c-215d-41c0-9485-264874398e77
-- statement:
--   Then $P(x)=\frac{n+1}{n-1}\left(x^n+(1-x)^n\right)-\frac 2{n-1}\left(x^{n+1}+(1-x)^{n+1}\right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32667 : ∀ n : ℕ, 1 < n → ∀ x : ℝ, (∑ k in Finset.range n, x^k) * (∑ k in Finset.range n, (1 - x)^k) = ((n + 1) / (n - 1)) * (x^n + (1 - x)^n) - (2 / (n - 1)) * (x^(n + 1) + (1 - x)^(n + 1))   :=  by sorry
