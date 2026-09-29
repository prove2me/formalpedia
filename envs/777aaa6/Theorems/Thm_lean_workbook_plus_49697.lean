-- Prove2me | Theorems.Thm_lean_workbook_plus_49697
-- name    : lean_workbook_plus_49697
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/128f8cdc-6b53-4146-bf20-f9e9e1c35f2b
-- statement:
--   Prove that for all $n>0,$ $F_{2n-1}=F_n^2 + F_{n-1}^2,$ where $F_n$ is the $n$ th Fibonacci number.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49697 (n : ℕ) : fib (2 * n - 1) = fib n ^ 2 + fib (n - 1) ^ 2   :=  by sorry
