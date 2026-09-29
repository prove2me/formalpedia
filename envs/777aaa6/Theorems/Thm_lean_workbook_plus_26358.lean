-- Prove2me | Theorems.Thm_lean_workbook_plus_26358
-- name    : lean_workbook_plus_26358
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/3f3a5654-e468-4dd4-bf5a-6a88eb746149
-- statement:
--   Prove $\frac{1}{x^{2}+x}= \frac{1}{x}-\frac{1}{x+1}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26358 : ∀ x : ℝ, x ≠ 0 ∧ x ≠ -1 → 1 / (x ^ 2 + x) = 1 / x - 1 / (x + 1)   :=  by sorry
