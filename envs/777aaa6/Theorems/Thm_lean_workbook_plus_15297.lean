-- Prove2me | Theorems.Thm_lean_workbook_plus_15297
-- name    : lean_workbook_plus_15297
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/20b76965-d7bf-4e1c-86ed-e6b845fecaa0
-- statement:
--   Suppose that $S = \{a_1, a_2, a_3, \hdots, a_n\}$ with $a_1 < a_2 < a_3 < \hdots < a_n.$ We are given the following: \n \n $${\begin{cases} \sum_{i=1}^{n-1} a_i = 32(n-1) = 32n-32, \ \sum_{i=2}^n a_i = 40(n-1) = 40n-40, \ \sum_{i=2}^{n-1} a_i = 35(n-2) = 35n-70, \ a_n-a_1 = 72 \implies a_1 + 72 = a_n. \end{cases}}$$ Subtracting the third equation from the sum of the first two, we find that \n \n $$\sum_{i=1}^n a_i = \left(32n-32\right) + \left(40n-40\right) - \left(35n-70\right) = 37n - 2.$$ Furthermore, from the fourth equation, we have \n \n $$\sum_{i=2}^{n} a_i - \sum_{i=1}^{n-1} a_i = \left[\left(a_1 + 72\right) + \sum_{i=2}^{n-1} a_i\right] - \left[\left(a_1\right) + \sum_{i=2}^{n-1} a_i\right] = \left(40n-40\right)-\left(32n-32\right).$$ Combining like terms and simplifying, we have \n \n $$72 = 8n-8 \implies 8n = 80 \implies n=10.$$ Thus, the sum of the elements in $S$ is $37 \cdot 10 - 2 = 368,$ and since there are 10 elements in $S,$ the average of the elements in $S$ is $\tfrac{368}{10}=36.8,$ yielding $\boxed{\textbf{(D)}}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15297  (n : ℕ)
  (a : ℕ → ℕ)
  (h₀ : 0 < n)
  (h₁ : ∀ i, 0 < i → a i < a (i + 1))
  (h₂ : ∑ i in Finset.range (n - 1), a i = 32 * (n - 1))
  (h₃ : ∑ i in Finset.range n, a i = 40 * (n - 1))
  (h₄ : ∑ i in Finset.range (n - 1), a i = 35 * (n - 2))
  (h₅ : a n - a 1 = 72) :
  ∑ i in Finset.range n, a i = 368   :=  by sorry
