-- Prove2me | Theorems.Thm_lean_workbook_plus_42812
-- name    : lean_workbook_plus_42812
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/5334d5d0-d1ff-4c66-831f-0439bea034d3
-- statement:
--   Prove that if none of the sums $a_1,a_1+a_2,a_1+a_2+a_3,\dotsc,a_1+\dotsc+a_{2018}$ are divisible by 2018, then there exists $m<n$ such that $a_m+a_{m+1}+\dotsc+a_n$ is divisible by 2018.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42812 (a : ℕ → ℤ) (h : ∀ i, ¬ 2018 ∣ (∑ j in Finset.range i, a j)) :
    ∃ m n, m < n ∧ 2018 ∣ (∑ j in Finset.Icc m n, a j)   :=  by sorry
