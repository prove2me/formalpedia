-- Prove2me | Theorems.Thm_lean_workbook_plus_12210
-- name    : lean_workbook_plus_12210
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/871b5d7d-7135-4a33-9156-7e85dbb21db9
-- statement:
--   Let $k$ be an even positive integer and define a sequence $<x_n>$ by $ x_1= 1 , x_{n+1} = k^{x_n} +1. $ Show that $x_n ^2$ divides $x_{n-1}x_{n+1}$ for each $n \geq 2.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12210 (k : ℕ) (x : ℕ → ℕ) (h₀ : x 1 = 1) (h₁ : ∀ n, x (n + 1) = k^(x n) + 1) (h₂ : 2 ∣ k) (n : ℕ) (hn : 2 ≤ n) : (x n)^2 ∣ (x (n - 1)) * (x (n + 1))   :=  by sorry
