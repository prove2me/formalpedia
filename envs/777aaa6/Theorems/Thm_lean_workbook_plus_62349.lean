-- Prove2me | Theorems.Thm_lean_workbook_plus_62349
-- name    : lean_workbook_plus_62349
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/e8fe8367-5861-46f5-8c6e-9ae777f5c6fe
-- statement:
--   Let $p\neq 3$ be a prime number. Show that there is a non-constant arithmetic sequence of positive integers $x_1,x_2,\ldots ,x_p$ such that the product of the terms of the sequence is a cube.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62349 (p : ℕ) (hp : p.Prime) (hp3 : p ≠ 3) : ∃ x : ℕ → ℕ, ∃ d : ℕ, ∀ n : ℕ, x (n + 1) - x n = d ∧ ∃ k : ℕ, ∏ i in Finset.range p, x i = k ^ 3   :=  by sorry
