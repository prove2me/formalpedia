-- Prove2me | Theorems.Thm_lean_workbook_plus_64729
-- name    : lean_workbook_plus_64729
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/b164c928-4a80-4211-9b62-720e90e260c6
-- statement:
--   If $ a_{1}, a_{2}, ..., a_{n}, b_{1} \leq b_{2} \leq ... \leq b_{n}$ positive numbers and $ a_{1} \leq b_{1} , a_{1} + a_{2} \leq b_{1} + b_{2}, ... , a_{1} + a_{2} + ... + a_{n} \leq b_{1} + b_{2} + ... + b_{n},$ prove $ \sqrt{a_{1}} + \sqrt{a_{2}} + ... + \sqrt{a_{n}} \leq \sqrt{b_{1}} + \sqrt{b_{2}} + ... + \sqrt{b_{n}}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64729 (n : ℕ) (a b : ℕ → ℝ) (h1 : ∀ i ∈ Finset.range n, 0 ≤ a i) (h2 : ∀ i ∈ Finset.range n, 0 ≤ b i) (h3 : ∀ i ∈ Finset.range n, a i ≤ b i) (h4 : ∀ i ∈ Finset.range n, (∑ k in Finset.range (i + 1), a k) ≤ ∑ k in Finset.range (i + 1), b k) : (∑ k in Finset.range n, Real.sqrt (a k)) ≤ ∑ k in Finset.range n, Real.sqrt (b k)   :=  by sorry
