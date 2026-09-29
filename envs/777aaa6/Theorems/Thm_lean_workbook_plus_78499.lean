-- Prove2me | Theorems.Thm_lean_workbook_plus_78499
-- name    : lean_workbook_plus_78499
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/0e8f509e-47eb-4e5f-b0e3-e138a03ce7a2
-- statement:
--   What is the value of $f(0!)+f(1!)+f(2!)+f(3!)+f(4!)$ given $f(n)=n-10\\left\\lfloor\\dfrac n{10}\\right\\rfloor$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78499 (f : ℕ → ℕ) (f_def : ∀ n, f n = n - 10 * Nat.floor (n / 10)) : f 0! + f 1! + f 2! + f 3! + f 4! = 14   :=  by sorry
