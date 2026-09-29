-- Prove2me | Theorems.Thm_lean_workbook_plus_25989
-- name    : lean_workbook_plus_25989
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/0ab3a4f9-1b4c-480e-9d4f-9244471c8e59
-- statement:
--   Prove that for every positive integer $m$, the Fibonacci sequence modulo $m$ is a periodic sequence.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25989 (m : ℕ) : ∃ n, ∀ k > n, fib k % m = fib (k + n) % m   :=  by sorry
