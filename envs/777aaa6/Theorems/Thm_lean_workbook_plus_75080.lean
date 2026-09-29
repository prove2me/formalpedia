-- Prove2me | Theorems.Thm_lean_workbook_plus_75080
-- name    : lean_workbook_plus_75080
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/707b287e-1bcd-4402-be8a-edbbd0041697
-- statement:
--   Prove the homogeneous inequality by induction:\nn \cdot (a_1 + ... + a_n) \cdot (\frac{1}{a_1} + ... + \frac{1}{a_n}) \geq n(n-2)^2 + \frac{4n^2(n-1)(a_1^2 + ... + a_n^2)}{(a_1 + ... + a_n)^2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75080  (n : ℕ)
  (a : ℕ → ℝ)
  (h₀ : 0 < n)
  (h₁ : 0 < a n)
  (h₂ : ∀ k, 0 < k → 0 < a k)
  (h₃ : ∀ k, a k ≠ a (k + 1))
  (h₄ : ∀ k, a k ≠ a (k - 1))
  (h₅ : 0 < ∑ k in Finset.range n, a k)
  (h₆ : 0 < ∑ k in Finset.range n, (1 / a k))
  : n * (∑ k in Finset.range n, a k) * (∑ k in Finset.range n, (1 / a k))
    ≥ n * (n - 2) ^ 2 + (4 * n ^ 2 * (n - 1) * (∑ k in Finset.range n, (a k) ^ 2)) / (∑ k in Finset.range n, a k) ^ 2   :=  by sorry
