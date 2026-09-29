-- Prove2me | Theorems.Thm_lean_workbook_plus_79195
-- name    : lean_workbook_plus_79195
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/1e78b483-4447-4618-8680-1b941d389886
-- statement:
--   Prove that $F_{n+1}^{2}-F_{n}^{2}-F_{n}F_{n+1} = (-1)^{n}$ for the Fibonacci series $F$, given $F_0 = 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79195 (n : ℕ) : (fib (n + 1))^2 - (fib n)^2 - fib n * fib (n + 1) = (-1 : ℤ)^n   :=  by sorry
