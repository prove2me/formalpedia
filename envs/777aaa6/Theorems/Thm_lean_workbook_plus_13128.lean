-- Prove2me | Theorems.Thm_lean_workbook_plus_13128
-- name    : lean_workbook_plus_13128
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/91b2528b-5f21-41d3-a461-2ee9886c0e83
-- statement:
--   Prove the identity $\sum_{n=0}^{k}(F_n)^2=F_k*F_{k+1}$, where $F_0=1$ and $F_n$ is the nth Fibonacci number with $F_1=F_2=1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13128 (k : ℕ) : ∑ n in Finset.range (k + 1), (fib n)^2 = fib k * fib (k + 1)   :=  by sorry
