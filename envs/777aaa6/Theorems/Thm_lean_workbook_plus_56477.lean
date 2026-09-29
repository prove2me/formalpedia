-- Prove2me | Theorems.Thm_lean_workbook_plus_56477
-- name    : lean_workbook_plus_56477
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/03756322-f6f9-443f-9699-16e73e822be4
-- statement:
--   Let $m = a+2b+c, n = a+b+2c$ and $p=a+b+3c$ . Then, we have $a = 5n-3p-m, b = m+p - 2n$ and $c = p-n$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56477 (a b c m n p : ℤ) : m = a + 2 * b + c ∧ n = a + b + 2 * c ∧ p = a + b + 3 * c ↔ a = 5 * n - 3 * p - m ∧ b = m + p - 2 * n ∧ c = p - n   :=  by sorry
