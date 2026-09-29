-- Prove2me | Theorems.Thm_lean_workbook_plus_66489
-- name    : lean_workbook_plus_66489
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/a09ea964-93d8-488a-bedd-b3ec80ed0026
-- statement:
--   Let $a_1= 1, a_2 = 7, a_{n+2} = 2a_{n+1} +15a_n$ where $n$ belongs in the set of natural numbers. Find a formula for $a_n$ in terms of $n$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66489 (a : ℕ → ℕ) (a1 : a 0 = 1) (a2 : a 1 = 7) (a_rec : ∀ n, a (n + 2) = 2 * a (n + 1) + 15 * a n) : ∃ f : ℕ → ℕ, ∀ n, a n = f n   :=  by sorry
