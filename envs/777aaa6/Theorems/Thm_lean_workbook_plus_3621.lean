-- Prove2me | Theorems.Thm_lean_workbook_plus_3621
-- name    : lean_workbook_plus_3621
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/0841a908-a18f-4e9d-a289-ddb647d73206
-- statement:
--   ok so we know that the sum of the first $n$ integers is $\frac{n\cdot(n+1)}{2}$. Thus the average is $\frac{n+1}{2}$. We know that this quantity must be slightly greater than $40\frac{3}{4}$ because subtracting out one number from a list of $n$ numbers and then finding the average should not have such a large impact. Thus we set $n=81$. The sum of the first $81$ numbers is $3321$ and $80\cdot40\frac{3}{4}=3260$. Thus $3321-3260=61$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3621  (n : ℕ)
  (h₀ : 0 < n)
  (h₁ : ∑ k in (Finset.range n), (k + 1) = 3321)
  (h₂ : ∑ k in (Finset.range (n - 1)), (k + 1) = 3260) :
  n = 81   :=  by sorry
