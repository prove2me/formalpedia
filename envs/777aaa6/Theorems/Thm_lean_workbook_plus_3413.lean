-- Prove2me | Theorems.Thm_lean_workbook_plus_3413
-- name    : lean_workbook_plus_3413
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/0dbee549-c42f-4a38-a3de-06084b532386
-- statement:
--   Derive $\binom{x}{2} = \frac{x^2 - x}{2}$ from the factorial definition of combinations.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3413 : ∀ x : ℕ, choose x 2 = (x^2 - x) / 2   :=  by sorry
