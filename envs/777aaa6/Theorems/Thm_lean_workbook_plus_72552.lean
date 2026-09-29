-- Prove2me | Theorems.Thm_lean_workbook_plus_72552
-- name    : lean_workbook_plus_72552
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/69d2a3a6-d47e-4f4f-bd0d-b63227402b11
-- statement:
--   Prove that $F_n$ divides $F_{2n}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72552 (n : ℕ) : fib n ∣ fib (2 * n)   :=  by sorry
