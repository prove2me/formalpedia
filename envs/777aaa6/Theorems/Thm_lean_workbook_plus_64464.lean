-- Prove2me | Theorems.Thm_lean_workbook_plus_64464
-- name    : lean_workbook_plus_64464
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/9ddd88d5-6727-45bb-8e68-af9ed48a8a78
-- statement:
--   $\frac 1{1-x}=\sum_{k=0}^{+\infty}x^k$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64464 : ∀ x : ℝ, |x| < 1 → 1 / (1 - x) = ∑' k : ℕ, x ^ k   :=  by sorry
