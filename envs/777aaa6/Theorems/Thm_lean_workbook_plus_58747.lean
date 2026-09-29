-- Prove2me | Theorems.Thm_lean_workbook_plus_58747
-- name    : lean_workbook_plus_58747
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/1dc5d072-a553-4722-8923-57ddd1f77075
-- statement:
--   Find the closed form of the sequence $a_1 = 4, a_2 = 7,$ and $a_{n+1} = 2a_n - a_{n-1} + 2$ for $n \geq 2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58747 (a : ℕ → ℝ) (a1 : a 0 = 4) (a2 : a 1 = 7) (a_rec : ∀ n, n ≥ 2 → a (n + 1) = 2 * a n - a (n - 1) + 2) : ∃ f : ℕ → ℝ, ∀ n, a n = f n   :=  by sorry
