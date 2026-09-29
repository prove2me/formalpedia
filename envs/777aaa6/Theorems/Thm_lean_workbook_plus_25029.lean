-- Prove2me | Theorems.Thm_lean_workbook_plus_25029
-- name    : lean_workbook_plus_25029
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/6d7393ae-2a4c-4074-b330-33dd64ac55b3
-- statement:
--   Given that real numbers $c_1,c_2,...,c_n$ satisfy $(n-1)(c_1^2+c_2^2+\cdots +c_n^2)=(c_1+c_2+\cdots +c_n)^2$ , prove that all of them are non positive or nonnegative.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25029 (n : ℕ) (c : ℕ → ℝ) (h : (n - 1) * (∑ i in Finset.range n, (c i) ^ 2) = (∑ i in Finset.range n, c i) ^ 2) : (∀ i ∈ Finset.range n, c i ≤ 0 ∨ 0 ≤ c i)   :=  by sorry
