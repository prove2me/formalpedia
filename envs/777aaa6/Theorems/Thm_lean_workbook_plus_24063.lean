-- Prove2me | Theorems.Thm_lean_workbook_plus_24063
-- name    : lean_workbook_plus_24063
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/93016e38-9961-41e9-abda-2cea42a93fd9
-- statement:
--   Prove that $a_n$ is an integer for all positive integers $n$ using the recurrence relation $a_{n+1} = 4a_n - a_{n-1}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24063 (a : ℕ → ℤ) (n : ℕ) (a0 : a 0 = 0) (a1 : a 1 = 1) (ha : ∀ n, a (n + 2) = 4 * a (n + 1) - a n) : ∀ n, IsIntegral ℤ (a n)   :=  by sorry
