-- Prove2me | Theorems.Thm_lean_workbook_plus_72115
-- name    : lean_workbook_plus_72115
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/d2abacfd-c9d4-440e-aba0-6547d4377dc9
-- statement:
--   If $ab=6\land a+b=2$ , then the equation $t^2-2t+6=0$ doesn't have real solutions.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72115 : a * b = 6 ∧ a + b = 2 → ¬ ∃ t : ℝ, t^2 - 2 * t + 6 = 0   :=  by sorry
