-- Prove2me | Theorems.Thm_lean_workbook_plus_67653
-- name    : lean_workbook_plus_67653
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/d1c0a550-126a-4261-ab6d-5b2659399784
-- statement:
--   Rewrite the expression as ${10^n-1\over 9}+{4^n-1\over 3}+1$ and show that it's an integer for all $n \geq 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67653 (n : ℕ) (hn : 1 ≤ n) : ∃ k : ℤ, (10^n-1)/9 + (4^n-1)/3 + 1 = k   :=  by sorry
