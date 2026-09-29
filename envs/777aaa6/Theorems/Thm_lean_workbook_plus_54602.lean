-- Prove2me | Theorems.Thm_lean_workbook_plus_54602
-- name    : lean_workbook_plus_54602
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/46acac99-138a-4d29-a208-8a9e7367752d
-- statement:
--   Find a closed form expression for $a_n$ in the sequence defined by $a_n=a_{n-1}^2-2$ with $a_0=3$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54602 (a : ℕ → ℤ) (a0 : a 0 = 3) (a_rec : ∀ n, a (n + 1) = a n ^ 2 - 2) : ∃ f : ℕ → ℤ, ∀ n, a n = f n   :=  by sorry
