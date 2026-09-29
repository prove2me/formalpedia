-- Prove2me | Theorems.Thm_lean_workbook_plus_62226
-- name    : lean_workbook_plus_62226
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/90d07cce-c563-4597-a7d3-740634efa74d
-- statement:
--   Prove that for all positive integers $n$ $ \sum_{k=0}^{n}{\binom{3n}{3k}} = \frac{1}{3}(2^{3n} + 2\cdot {(-1)}^n) $ holds.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62226 (n : ℕ) : ∑ k in Finset.range (n+1), (Nat.choose (3*n) (3*k)) = 1/3 * (2^(3*n) + 2 * (-1 : ℤ)^n)   :=  by sorry
