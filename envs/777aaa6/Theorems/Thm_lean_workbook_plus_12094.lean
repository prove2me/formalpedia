-- Prove2me | Theorems.Thm_lean_workbook_plus_12094
-- name    : lean_workbook_plus_12094
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/b2802151-90d5-40c3-9f00-42ddaf35074b
-- statement:
--   Same idea, except contradiction: Suppose neither inequality is true; i.e.\n\n$\sum_{i=1}^{n} \frac{a_i}{b_i} < n \\\sum_{i=1}^{n} \frac{b_i}{a_i} < n$\n\nthen we have\n\n$\sum_{i=1}^n \left(\frac{a_i}{b_i} + \frac{b_i}{a_i}\right) < 2n$.\n\nBut $\frac{a_i}{b_i} + \frac{b_i}{a_i} > 2$ by AM-GM, so we have a contradiction.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12094  (a b : ℕ → ℝ)
  (n : ℕ)
  (h₀ : 0 < n)
  (h₁ : ∀ i, 0 < a i ∧ 0 < b i)
  (h₂ : ∑ i in Finset.range n, (a i / b i) < n)
  (h₃ : ∑ i in Finset.range n, (b i / a i) < n) :
  ∑ i in Finset.range n, (a i / b i + b i / a i) < 2 * n   :=  by sorry
