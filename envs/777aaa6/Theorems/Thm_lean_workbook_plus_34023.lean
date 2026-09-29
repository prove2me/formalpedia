-- Prove2me | Theorems.Thm_lean_workbook_plus_34023
-- name    : lean_workbook_plus_34023
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/b6e1de44-d17c-498a-812f-5b78ec113fc3
-- statement:
--   Let $ n$ be a positive integer. Prove that at least two numbers of $ \sqrt{n},\ \sqrt{n+1},\ \sqrt{n+2}$ are irrational numbers.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34023 (n : ℕ) (hn : 0 < n) : ∃ k : Fin 3, ¬ ∃ a : ℚ, (k : ℝ) = √(n + k)   :=  by sorry
