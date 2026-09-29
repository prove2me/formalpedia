-- Prove2me | Theorems.Thm_lean_workbook_plus_9388
-- name    : lean_workbook_plus_9388
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/107800e5-ce02-4327-a9f0-95a0daeb3c49
-- statement:
--   Find the roots of the equation $ x^2-(a^2-a+1)(x-b^2-1)-(b^2+1)^2=0 $.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9388 (a b : ℝ) : (x^2 - (a^2 - a + 1) * (x - b^2 - 1) - (b^2 + 1)^2 = 0) ↔ (x = a^2 - a - b^2) ∨ (x = b^2 + 1)   :=  by sorry
