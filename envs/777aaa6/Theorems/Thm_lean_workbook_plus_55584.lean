-- Prove2me | Theorems.Thm_lean_workbook_plus_55584
-- name    : lean_workbook_plus_55584
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/6f7e299c-e5c0-4ff8-b33f-d51bcdcaa185
-- statement:
--   Prove that $ 1-\frac{1}{2}+\frac{1}{3}-\frac{1}{4}+...+\frac{1}{2n-1}-\frac{1}{2n}=\frac{1}{n+1}+\frac{1}{n+2}+...+\frac{1}{2n}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55584 : ∀ n : ℕ, (∑ k in Finset.range (2 * n), (-1 : ℤ)^k / (k + 1)) = (∑ k in Finset.Icc (n + 1) (2 * n), 1 / k)   :=  by sorry
