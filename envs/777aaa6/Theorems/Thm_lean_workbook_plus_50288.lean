-- Prove2me | Theorems.Thm_lean_workbook_plus_50288
-- name    : lean_workbook_plus_50288
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/867c46c8-941f-417a-96e4-ef0b4de3c488
-- statement:
--   We can use the binomial theorem: \n $(x+y)^{n}=x^{n}\binom{n}{0}+x^{n-1}\binom{n}{1}+\cdot\cdot\cdot+y^{n}\binom{n}{n}$ \nAnd we plug in 1 for x and y. \n $\boxed{2^{n}=\binom{n}{0}+\binom{n}{1}+\cdot\cdot\cdot+\binom{n}{n}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50288 (n : ℕ) : 2^n = ∑ k in Finset.range (n+1), (Nat.choose n k)   :=  by sorry
