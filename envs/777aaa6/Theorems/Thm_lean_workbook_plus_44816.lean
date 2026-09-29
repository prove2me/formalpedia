-- Prove2me | Theorems.Thm_lean_workbook_plus_44816
-- name    : lean_workbook_plus_44816
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/d635e490-1416-4388-90ca-4a19bfabef2d
-- statement:
--   Prove that the sequence $ (b_n)_{n\geq 0}$ given by $ b_0 = - 1$ , $ b_1 = 1$ and $ b_{n + 1} = 4b_n - b_{n - 1}$ satisfies $ 2a_n - 1 = b_n^2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44816 (n : ℕ) (a : ℕ → ℕ) (b : ℕ → ℤ) (h₁ : a 0 = 1) (h₂ : b 0 = -1) (h₃ : b 1 = 1) (h₄ : ∀ n, b (n + 1) = 4 * b n - b (n - 1)) (h₅ : ∀ n, a (n + 1) = a n + b (n + 1)) : 2 * a n - 1 = b n ^ 2   :=  by sorry
