-- Prove2me | Theorems.Thm_lean_workbook_plus_65291
-- name    : lean_workbook_plus_65291
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/6c67d89a-0c97-4e8d-abb1-ea6dd1e7f70b
-- statement:
--   Prove that for any prime $p$ there is a Fibonacci number divisible by $p$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65291 (p : ℕ) (hp : p.Prime) : ∃ n, p ∣ fib n   :=  by sorry
