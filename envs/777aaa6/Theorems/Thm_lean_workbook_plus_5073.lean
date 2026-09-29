-- Prove2me | Theorems.Thm_lean_workbook_plus_5073
-- name    : lean_workbook_plus_5073
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/3071e48e-fa6d-48b8-8f4e-1bbfd6a294b2
-- statement:
--   Claim: For any $n$ , we can find $a_k$ for $1 \le k \le n$ such that $\sum_{k=1}^n \frac{1}{ka_k} = \frac{n}{n+1}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5073 (n : ℕ) : ∃ a : ℕ → ℕ, ∀ k, 1 ≤ k ∧ k ≤ n → (∑ i in Finset.Icc 1 n, (1/(i * a i)) = n/(n+1))   :=  by sorry
