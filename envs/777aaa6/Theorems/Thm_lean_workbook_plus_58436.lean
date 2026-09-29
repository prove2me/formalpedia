-- Prove2me | Theorems.Thm_lean_workbook_plus_58436
-- name    : lean_workbook_plus_58436
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/0ce8f46a-fe70-4073-9ecc-172017be8354
-- statement:
--   Prove that for all $n\ge 3$ there are $n$ different positive integers $x_1,x_2, ...,x_n$ such that $\frac{1}{x_1}+\frac{1}{x_2}+...+\frac{1}{x_n}= 1.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58436 (n : ℕ) (hn : 3 ≤ n) : ∃ x : ℕ → ℕ, (∀ i, 0 < x i ∧ ∀ i, x i ≠ x j) ∧ ∑ i in Finset.range n, (1 / x i) = 1   :=  by sorry
