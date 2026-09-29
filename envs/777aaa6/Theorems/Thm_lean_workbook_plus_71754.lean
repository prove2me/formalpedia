-- Prove2me | Theorems.Thm_lean_workbook_plus_71754
-- name    : lean_workbook_plus_71754
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/6525e603-824c-4c24-ba46-1595b4664dcb
-- statement:
--   Thus, $ f(100) = 9(2) + 90(3) + 1(4) = \boxed{292}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71754  (f : ℕ → ℕ)
  (h₀ : ∀ n, 1 ≤ n ∧ n ≤ 100 → f n = 9 * 2 + 90 * 3 + 1 * 4) :
  f 100 = 292   :=  by sorry
