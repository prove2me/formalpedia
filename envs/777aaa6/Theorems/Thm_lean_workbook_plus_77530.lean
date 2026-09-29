-- Prove2me | Theorems.Thm_lean_workbook_plus_77530
-- name    : lean_workbook_plus_77530
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/0f674515-edfd-49ae-934d-bfe053d24b3b
-- statement:
--   Find a closed form expression for $a_n$ given the recurrence relation $a_{n+1}a_{n-1} = a_n^2 + 5$ with initial conditions $a_1 = 1$ and $a_2 = 2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77530 (a : ℕ → ℝ) (a1 : a 1 = 1) (a2 : a 2 = 2) (a_rec : ∀ n, a (n + 1) * a (n - 1) = a n ^ 2 + 5) : ∃ f : ℕ → ℝ, ∀ n, a n = f n   :=  by sorry
