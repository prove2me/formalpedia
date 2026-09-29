-- Prove2me | Theorems.Thm_lean_workbook_plus_62603
-- name    : lean_workbook_plus_62603
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/27b08b12-38f0-4593-8219-54c4a02bc8e1
-- statement:
--   Prove that $a_n = x_n \cdot m + y_n - 1$ where $x_n, y_n$ are defined by $x_0=0, x_1=y_1=1, y_2=2$ and $x_{n+1}=4x_n-x_{n-1}$ as well as $y_{n+1}=4y_n-y_{n-1}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62603 (m : ℕ) (a : ℕ → ℕ) (x : ℕ → ℕ) (y : ℕ → ℕ) (h₀ : x 0 = 0) (h₁ : x 1 = 1) (h₂ : y 1 = 1) (h₃ : y 2 = 2) (h₄ : ∀ n, x (n + 2) = 4 * x (n + 1) - x n) (h₅ : ∀ n, y (n + 2) = 4 * y (n + 1) - y n) (h₆ : ∀ n, a n = x n * m + y n - 1) : ∀ n, a n = x n * m + y n - 1   :=  by sorry
