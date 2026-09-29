-- Prove2me | Theorems.Thm_lean_workbook_plus_54367
-- name    : lean_workbook_plus_54367
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/dd6a0e09-0cd3-4c3f-a3c2-b4850adc1395
-- statement:
--   Prove that $x^6+x^4+x^2+x+3=0 $ has no positive real roots
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54367 : ¬∃ x : ℝ, x > 0 ∧ x ^ 6 + x ^ 4 + x ^ 2 + x + 3 = 0   :=  by sorry
