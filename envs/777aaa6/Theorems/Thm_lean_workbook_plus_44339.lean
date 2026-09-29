-- Prove2me | Theorems.Thm_lean_workbook_plus_44339
-- name    : lean_workbook_plus_44339
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/f3580332-1056-4f40-9bf9-b95e7e7688b6
-- statement:
--   Prove that $x_n=a_n^2+b_n^2$ where $a_n=5(a_{n-1}-a_{n-2})+a_{n-3}$ with $a_0=a_1=0, a_2=2$ and $b_n=a_n+1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44339 (x : ℕ → ℕ) (a : ℕ → ℕ) (b : ℕ → ℕ) (n : ℕ) (h₀ : x n = a n ^ 2 + b n ^ 2) (h₁ : a n = 5 * (a (n - 1) - a (n - 2)) + a (n - 3)) (h₂ : a 0 = 0) (h₃ : a 1 = 0) (h₄ : a 2 = 2) (h₅ : b n = a n + 1) : x n = a n ^ 2 + b n ^ 2   :=  by sorry
