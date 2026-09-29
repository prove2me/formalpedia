-- Prove2me | Theorems.Thm_lean_workbook_plus_45064
-- name    : lean_workbook_plus_45064
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/d63a4db5-6ee2-45fc-9355-f7e8354783c0
-- statement:
--   Prove that the only infinite sequence $a_1,a_2,...,a_n$ of positive numbers (not necessarily integers) such that the equality $a_1^3+a_2^3+...+a_n^3=(a_1+a_2+...+a_n)^2$ holds for every positive integer $n$ is the sequence given by $a_n=n$ for $n=1,2,3,...$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45064 (a : ℕ → ℝ) (ha : ∀ n : ℕ, 0 < a n) (hab : ∀ n : ℕ, (∑ i in Finset.range n, (a i)^3) = (∑ i in Finset.range n, a i)^2) : ∀ n : ℕ, a n = n   :=  by sorry
