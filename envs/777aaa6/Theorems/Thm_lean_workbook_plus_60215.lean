-- Prove2me | Theorems.Thm_lean_workbook_plus_60215
-- name    : lean_workbook_plus_60215
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/03bb86fd-ea23-4124-8428-6565a4209f15
-- statement:
--   Let $(a_n), n = 0, 1, . . .,$ be a sequence of real numbers such that $a_0 = 0$ and $a^3_{n+1} = \frac{1}{2} a^2_n -1, n= 0, 1,\cdots$. Prove that there exists a positive number $q, q < 1$ , such that for all $n = 1, 2, \ldots ,$ $|a_{n+1} - a_n| \leq q|a_n - a_{n-1}|,$ and give one such $q$ explicitly.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60215 (a : ℕ → ℝ) (ha : a 0 = 0) (ha_rec : ∀ n, a (n + 1) = (1 / 2 * (a n)^2 - 1)^(1 / 3)) : ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∀ n, 1 ≤ n → abs (a (n + 1) - a n) ≤ q * abs (a n - a (n - 1))   :=  by sorry
