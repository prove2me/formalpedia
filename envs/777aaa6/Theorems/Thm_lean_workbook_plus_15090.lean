-- Prove2me | Theorems.Thm_lean_workbook_plus_15090
-- name    : lean_workbook_plus_15090
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/4235b42f-024a-425c-991f-fd514a155f84
-- statement:
--   Determine the convergence of the series: $\sum_{n = 1}^{\infty}\arcsin\left(\frac{n-1}{n^2-n+1}\right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15090 : ∀ n : ℕ, n ≥ 1 → 0 ≤ ∑ k in Finset.range n, Real.arcsin ((k:ℝ) - 1) / (k ^ 2 - k + 1) ∧ ∑' k : ℕ, Real.arcsin ((k:ℝ) - 1) / (k ^ 2 - k + 1) ≤ π / 2   :=  by sorry
