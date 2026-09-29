-- Prove2me | Theorems.Thm_lean_workbook_plus_32478
-- name    : lean_workbook_plus_32478
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/dd2e700a-1c31-44d8-8bdd-b1840a265646
-- statement:
--   Let $T(n)$ be the number of permutations, $(P_{1}, P_{2}, ..., P_{n})$ of (1,2,...,n) such that for any integer $k, 1 \leq k \leq n, (P_{1}, P_{2}, ..., P_{k})$ does not form a permutation of (1,2,...,k). a) Prove that $T(n)=n!-\sum_{i=1}^{n-1} T(i)(n-i)!$. b) Using a) or otherwise, find $T(6)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32478 {T : ℕ → ℕ} (h₁ : T 0 = 1) (h₂ : ∀ n, T (n + 1) = n! - ∑ i in Finset.range n, T i * (n - i)!): T 6 = 1385 - 7!/2! - 6!/3! - 5!/4! - 4!/5! - 3!/6! - 2!/7! - 1!/8!   :=  by sorry
