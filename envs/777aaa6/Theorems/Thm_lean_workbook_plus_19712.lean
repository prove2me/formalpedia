-- Prove2me | Theorems.Thm_lean_workbook_plus_19712
-- name    : lean_workbook_plus_19712
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/d4a70000-719a-438e-8675-b04cd90813cd
-- statement:
--   Prove that for every natural number $n > 1$ $ \frac{1}{n+1} \left( 1 + \frac{1}{3} +\frac{1}{5} + \ldots + \frac{1}{2n-1} \right) > \frac{1}{n} \left( \frac{1}{2} + \frac{1}{4} + \ldots + \frac{1}{2n} \right) . $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19712 : ∀ n : ℕ, 1 < n → (1 / (n + 1)) * ∑ i in Finset.range n, (1 / (2 * i + 1)) > (1 / n) * ∑ i in Finset.range n, (1 / (2 * i + 2))   :=  by sorry
