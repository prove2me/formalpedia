-- Prove2me | Theorems.Thm_lean_workbook_plus_70290
-- name    : lean_workbook_plus_70290
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/abc304ee-5363-4fb7-b78b-ad15fe83b1c6
-- statement:
--   Prove that for any positive integer n, there exist a Fibonacci Number $F_m$ such that $n \; | \; F_m$ and $m \le n^2-1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70290 (n : ℕ) : ∃ m ≤ n^2-1, n ∣ fib m   :=  by sorry
