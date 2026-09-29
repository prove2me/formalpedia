-- Prove2me | Theorems.Thm_lean_workbook_plus_77088
-- name    : lean_workbook_plus_77088
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/09ee188f-8201-42d8-b77f-453c00441e22
-- statement:
--   Prove that $ F_n F_{n+1} + F_{n-1} F_n = F_{2n}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77088 (n : ℕ) : fib n * fib (n + 1) + fib (n - 1) * fib n = fib (2 * n)   :=  by sorry
