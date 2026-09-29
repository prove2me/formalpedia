-- Prove2me | Theorems.Thm_lean_workbook_plus_26503
-- name    : lean_workbook_plus_26503
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/db4fad11-1e29-4e16-922b-ab055020462e
-- statement:
--   Prove the relationship among Fibonacci numbers: $F_{n+1}F_{n-1}=F_{n}^2-(-1)^{n}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26503 : ∀ n : ℕ, (fib (n + 1) : ℤ) * fib (n - 1) = fib n ^ 2 - (-1) ^ n   :=  by sorry
