-- Prove2me | Theorems.Thm_lean_workbook_plus_34706
-- name    : lean_workbook_plus_34706
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/afdcfa21-a4cc-4da0-b4eb-3777e8bfb031
-- statement:
--   Find the formula for the sequence $(x_n)_{n\in\mathbb{N}}$ defined by $x_1=\frac{1}{2}$ and $x_{n+1}={x_n}^2+1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34706 (x : ℕ → ℝ) (x1 : x 0 = 1 / 2) (xn : ∀ n, x (n + 1) = (x n)^2 + 1) : ∃ f : ℕ → ℝ, ∀ n, x n = f n   :=  by sorry
