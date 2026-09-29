-- Prove2me | Theorems.Thm_lean_workbook_plus_40830
-- name    : lean_workbook_plus_40830
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/c3123a4d-c0a6-4914-9d68-a6f37d4d384b
-- statement:
--   Prove that the sum of binomial coefficients multiplied by powers of 10 is equal to \(11^n\): \(\binom{n}{0}10^n + \binom{n}{1}10^{n-1} + \dots + \binom{n}{n}10^0 = 11^n\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40830 (n : ℕ) : ∑ k in Finset.range (n+1), (n.choose k) * (10:ℕ)^(n-k) = 11^n   :=  by sorry
