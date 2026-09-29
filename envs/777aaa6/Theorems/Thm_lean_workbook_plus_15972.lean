-- Prove2me | Theorems.Thm_lean_workbook_plus_15972
-- name    : lean_workbook_plus_15972
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/a8c07b87-abfd-404f-b16a-4094c28fad3b
-- statement:
--   Prove: $F_{2n-1}=F_{n}F_{n+1}-F_{n-1}F_{n-2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15972 (n : ℕ) : fib (2 * n - 1) = fib n * fib (n + 1) - fib (n - 1) * fib (n - 2)   :=  by sorry
