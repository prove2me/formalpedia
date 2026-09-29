-- Prove2me | Theorems.Thm_lean_workbook_plus_77339
-- name    : lean_workbook_plus_77339
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/8513269c-704a-4efe-a4db-f7ea2789802a
-- statement:
--   Let $ a_n = \frac {1}{4n + 1} + \frac {1}{4n + 3} - \frac {1}{2n + 2} + \frac {n^2}{3^n} + \frac {cos(n)}{1 + n^2} ,n = 0,1,2,..,$ Does the infinite series $ \sum_{n = 0}^{ + \infty}{a_n}$ converge and if so , What is its sum ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77339 : ∃ y, ∑' n : ℕ, (1 / (4 * n + 1) + 1 / (4 * n + 3) - 1 / (2 * n + 2) + n ^ 2 / 3 ^ n + cos n / (1 + n ^ 2)) = y   :=  by sorry
