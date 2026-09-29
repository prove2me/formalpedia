-- Prove2me | Theorems.Thm_lean_workbook_plus_55190
-- name    : lean_workbook_plus_55190
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/44dfd859-ca68-4d83-89b1-830b99f70caa
-- statement:
--   Prove that any two consecutive Fibonacci numbers $ F_k$ and $ F_{k+1}$ are relatively prime.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55190 (k : ℕ) : Nat.Coprime (fib k) (fib (k + 1))   :=  by sorry
