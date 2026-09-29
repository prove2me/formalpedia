-- Prove2me | Theorems.Thm_lean_workbook_plus_10404
-- name    : lean_workbook_plus_10404
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/003f67ad-59ab-4977-9552-e6179872c9c6
-- statement:
--   Prove the Binomial Theorem: $(x+y)^n=\sum_{k=0}^n{n\choose k}x^{n-k}y^k$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10404 (n : ℕ) (x y : ℝ) : (x + y) ^ n = ∑ k in Finset.range (n + 1), (n.choose k) * x ^ (n - k) * y ^ k   :=  by sorry
