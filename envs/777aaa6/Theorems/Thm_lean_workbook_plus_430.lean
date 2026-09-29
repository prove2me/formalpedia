-- Prove2me | Theorems.Thm_lean_workbook_plus_430
-- name    : lean_workbook_plus_430
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/479bc05b-f74d-4ef2-9b8b-3515499290e9
-- statement:
--   Prove that $F_{n+2}^2 - F_{n+1} \cdot F_{n+2} - F_{n+1}^2 = (-1)^{n+1}$ using the given Fibonacci sequence relation $F_0=0, F_1=1, F_{n+1}=F_n+F_{n-1}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_430 (n : ℕ) : (fib (n + 2))^2 - fib (n + 1) * fib (n + 2) - (fib (n + 1))^2 = (-1 : ℤ)^(n + 1)   :=  by sorry
