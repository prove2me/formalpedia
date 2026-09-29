-- Prove2me | Theorems.Thm_lean_workbook_plus_50385
-- name    : lean_workbook_plus_50385
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/47977e9b-c3f1-4389-96c8-a46bed3a9eef
-- statement:
--   Let $x_2>0$ and $x_{n+1}=-1+\sqrt[n]{1+nx_n}$ for $n\geq 2$ . Prove $nx_n\to 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50385 (x : ℕ → ℝ) (x2 : 0 < x 2) (h : ∀ n, x (n + 1) = -1 + (1 + n * x n) ^ (1 / n)) : ∀ ε, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n → |n * x n| < ε   :=  by sorry
