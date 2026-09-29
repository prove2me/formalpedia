-- Prove2me | Theorems.Thm_lean_workbook_plus_72995
-- name    : lean_workbook_plus_72995
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/db89cfea-f3a1-49ea-bc21-c298d3424fec
-- statement:
--   Solve for the given recursive formula $ a_{n+1} = \frac{1}{4-3a_n} $ to find an explicit expression for $ a_n $ in terms of $ a_1 $.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72995 (a : ℕ → ℝ) (a1 : ℝ) (h1 : a1 = a 0) (h2 : ∀ n, a (n + 1) = 1 / (4 - 3 * a n)) : ∃ f : ℕ → ℝ, ∀ n, a n = f n   :=  by sorry
