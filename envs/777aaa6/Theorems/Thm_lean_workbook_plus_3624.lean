-- Prove2me | Theorems.Thm_lean_workbook_plus_3624
-- name    : lean_workbook_plus_3624
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/19502d96-e404-423b-bb2e-d0997e126e73
-- statement:
--   Solving a similar system we have $(x - 1) + (x - 2) + ... + 1 = (x + 1) + (x + 2) + ... + n$ . This becomes $\frac{x(x - 1)}{2} = \frac{n(n + 1)}{2} - \frac{x(x + 1)}{2}$ . So $x(x - 1) + x(x + 1) = n^2 + n$ . Hence $\frac{n(n + 1)}{2} = x^2$ . Note that taking $n = 49$ gives us $49 \cdot 25 = x^2$ , so $x = \boxed{35}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3624  (x n : ℕ)
  (h₀ : 0 < n ∧ 0 < x)
  (h₁ : ∑ k in Finset.Icc 1 n, k = ∑ k in Finset.Icc 1 x, k)
  (h₂ : n = 49) :
  x = 35   :=  by sorry
