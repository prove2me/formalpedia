-- Prove2me | Theorems.Thm_lean_workbook_plus_68462
-- name    : lean_workbook_plus_68462
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/9cdb5415-4c60-470f-a314-69b07bbe710e
-- statement:
--   prove that if $a,b,c$ are positive numbers and $abc = 1$ ,then, $ \frac{a}{2b+c} + \frac{b}{2c+a} +\frac{c}{2a+b} \ge 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68462 (a b c : ℝ) (ha : a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b * c = 1) :
  a / (2 * b + c) + b / (2 * c + a) + c / (2 * a + b) ≥ 1   :=  by sorry
