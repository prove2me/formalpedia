-- Prove2me | Theorems.Thm_lean_workbook_plus_60488
-- name    : lean_workbook_plus_60488
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/0448202e-e2b3-4d97-bda4-2a106076ccc9
-- statement:
--   $$\left(\sum_{i=1}^n i\right)^2 = \left(\sum_{i=1}^n \dbinom{i}{1} \right)^2$$ $$=\dbinom{n+1}{2}^2$$ $$=\left(\frac{(n+1)n}{2} \right)^2$$ $$=\frac{1}{4}n^4+\frac{1}{2}n^3+\frac{1}{4}n^2.$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60488 :  ∀ n : ℕ, (∑ i in Finset.range (n + 1), i)^2 = (∑ i in Finset.range (n + 1), choose i 1)^2 ∧ (∑ i in Finset.range (n + 1), choose i 1)^2 = choose (n + 1) 2 ^ 2 ∧ choose (n + 1) 2 ^ 2 = ((n + 1) * n / 2)^2 ∧ ((n + 1) * n / 2)^2 = n^4 / 4 + n^3 / 2 + n^2 / 4   :=  by sorry
