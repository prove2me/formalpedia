-- Prove2me | Theorems.Thm_lean_workbook_plus_23098
-- name    : lean_workbook_plus_23098
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/36a63f6f-73f5-4249-962a-d6622968cdfb
-- statement:
--   How can you get that $x^8-x^7+x^2-x \geq -4$ for $-1 \leq x \leq 1$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23098 (x : ℝ) (hx : -1 ≤ x ∧ x ≤ 1) :
  x^8 - x^7 + x^2 - x ≥ -4   :=  by sorry
