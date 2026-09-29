-- Prove2me | Theorems.Thm_lean_workbook_plus_74653
-- name    : lean_workbook_plus_74653
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/aad8fbb6-ecba-4d5e-8ccf-1aee0ce9ce5f
-- statement:
--   Binomial formula. If $ a$ and $ b$ are two elements of a field $ K$ , and $ n$ is a nonnegative integer, then $ \left(a+b\right)^n=\sum_{k=0}^n\binom{n}{k}a^kb^{n-k}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74653 {K : Type*} [Field K] (a b : K) (n : ℕ) : (a + b) ^ n = ∑ k in Finset.range (n + 1), choose n k * a ^ k * b ^ (n - k)   :=  by sorry
