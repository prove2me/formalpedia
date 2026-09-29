-- Prove2me | Theorems.Thm_lean_workbook_plus_66404
-- name    : lean_workbook_plus_66404
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/a4b39662-f75c-4d45-a8f1-5e44b9a15643
-- statement:
--   Case 2: $ -1 \leq x < 1$ Now, both factors are obviously negative or $0$ . However, the product of these factors is nonnegative.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66404 ∀ x: ℝ, -1 ≤ x ∧ x < 1 → 0 ≤ (x+1)*(x-1)   :=  by sorry
