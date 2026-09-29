-- Prove2me | Theorems.Thm_lean_workbook_plus_71370
-- name    : lean_workbook_plus_71370
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/e88b83ef-fc5b-467e-88b0-af9f199f7556
-- statement:
--   Rewrite as\n\n$\\sum_{i=0}^{n}{\\binom{n+i}{n-i}}=F_{2n+1}.$ LHS counts over the number of length 2 steps done. RHS trivially also counts the number of ways to walk up the staircase.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71370 : ∀ n : ℕ, ∑ i in Finset.range (n+1), choose (n+i) (n-i) = fib 2*n + 1   :=  by sorry
