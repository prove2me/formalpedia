-- Prove2me | Theorems.Thm_lean_workbook_plus_42439
-- name    : lean_workbook_plus_42439
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/3d8e8fbd-5399-446d-8127-4810c8b967f4
-- statement:
--   Prove that: $\sum\limits_{k=0}^n\frac{(2k-1)!!\cdot (2n-2k-1)!!}{(2n)!!}\dbinom nk=1.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42439 : ∀ n : ℕ, ∑ k in Finset.range (n+1), ((2 * k - 1).factorial * (2 * n - 2 * k - 1).factorial) / (2 * n).factorial * (n.choose k) = 1   :=  by sorry
