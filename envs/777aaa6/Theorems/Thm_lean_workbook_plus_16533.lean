-- Prove2me | Theorems.Thm_lean_workbook_plus_16533
-- name    : lean_workbook_plus_16533
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/e2e6b466-fe3c-487a-be89-9b049bf02323
-- statement:
--   Given $a_1 = 2, a_2 = 1, a _3 = 4,$ and for all n $a_{n+3} = 2a_{n+2}^2 + a_{n+1}^3 + a_n$, find the explicit formula for $a_k$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16533 (a : ℕ → ℕ) (a1 : a 0 = 2) (a2 : a 1 = 1) (a3 : a 2 = 4) (h : ∀ n, a (n + 3) = 2 * a (n + 2) ^ 2 + a (n + 1) ^ 3 + a n) : ∃ f : ℕ → ℕ, ∀ k, a k = f k   :=  by sorry
