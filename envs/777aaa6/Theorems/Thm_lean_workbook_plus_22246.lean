-- Prove2me | Theorems.Thm_lean_workbook_plus_22246
-- name    : lean_workbook_plus_22246
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/1df69187-1e75-4280-9834-4e6a6fb95bda
-- statement:
--   Prove that the sum of the squares of the first $n$ natural numbers is $\frac{n(n+1)(2n+1)}{6}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22246 : ∀ n : ℕ, ∑ i in Finset.range n, i^2 = n * (n + 1) * (2 * n + 1) / 6   :=  by sorry
