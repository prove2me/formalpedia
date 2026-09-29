-- Prove2me | Theorems.Thm_lean_workbook_plus_55354
-- name    : lean_workbook_plus_55354
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/c9408965-d271-44d4-9200-d6e6929a0350
-- statement:
--   Given the sequence $a_1=1$ and $a_{n+1}=\frac{{a_n}^2+3}{a_n+1}$, find the formula for $a_n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55354 (a : ℕ → ℚ) (a1 : a 0 = 1) (a_rec : ∀ n, a (n + 1) = (a n ^ 2 + 3) / (a n + 1)) : ∃ f : ℕ → ℚ, ∀ n, a n = f n   :=  by sorry
