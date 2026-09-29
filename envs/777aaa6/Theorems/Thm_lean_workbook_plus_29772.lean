-- Prove2me | Theorems.Thm_lean_workbook_plus_29772
-- name    : lean_workbook_plus_29772
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/48ff35ef-33ca-4186-9e18-39ecbf2be056
-- statement:
--   Prove that for the sequence of Fibonacci numbers we have $ F_0+F_1+ \cdots + F_n = F_{n+2} -1 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29772 (n : ℕ) : ∑ k in Finset.range (n+1), fib k = fib (n+2) - 1   :=  by sorry
