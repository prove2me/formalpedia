-- Prove2me | Theorems.Thm_lean_workbook_plus_61921
-- name    : lean_workbook_plus_61921
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/54e71ffc-f3ec-44b5-beb4-1556d90b15ba
-- statement:
--   Prove that $\sum_{k=0}^{n}F^{2}_{k}=F_{n}F_{n+1}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61921 (n : ℕ) : ∑ k in Finset.range (n+1), fib k ^ 2 = fib n * fib (n + 1)   :=  by sorry
