-- Prove2me | Theorems.Thm_lean_workbook_plus_42239
-- name    : lean_workbook_plus_42239
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/ac645571-b09e-4d59-aca2-aecd9f840947
-- statement:
--   Given that $a_1 = 1, a_2 = 2, a_3 = 2$ , and that $a_{n+3} = a_{n+2} + a_{n+1} - 2a_n$ find the explicit formula for $a_k$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42239 (a : ℕ → ℕ) (a1 : a 0 = 1) (a2 : a 1 = 2) (a3 : a 2 = 2) (a_rec : ∀ n, a (n + 3) = a (n + 2) + a (n + 1) - 2 * a n) : ∃ f : ℕ → ℕ, ∀ k, a k = f k   :=  by sorry
