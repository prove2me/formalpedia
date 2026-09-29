-- Prove2me | Theorems.Thm_lean_workbook_plus_53966
-- name    : lean_workbook_plus_53966
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/0666ad2c-3c93-4c07-a3d3-fb9b6508d24c
-- statement:
--   Find a closed form for the sequence defined by $a_n=2a_{n-1}+a_{n-2}$ with initial conditions $a_0=1, a_1=3$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53966 (a : ℕ → ℝ) (a0 : a 0 = 1) (a1 : a 1 = 3) (a_rec : ∀ n, a (n + 2) = 2 * a (n + 1) + a n) : ∃ f : ℕ → ℝ, ∀ n, a n = f n   :=  by sorry
