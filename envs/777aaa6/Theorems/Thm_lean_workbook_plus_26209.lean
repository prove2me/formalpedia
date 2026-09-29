-- Prove2me | Theorems.Thm_lean_workbook_plus_26209
-- name    : lean_workbook_plus_26209
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/0f4cccfa-b7e1-412e-a637-b431bf0ae6f2
-- statement:
--   There exists a simple proof after using the inequality: $$\sqrt{2(a^2+b^2)(b^2+c^2)(c^2+a^2)}\ge (a+b)(b+c)(c+a)-4abc$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26209 (a b c : ℝ) :
  Real.sqrt (2 * (a ^ 2 + b ^ 2) * (b ^ 2 + c ^ 2) * (c ^ 2 + a ^ 2)) ≥
    (a + b) * (b + c) * (c + a) - 4 * a * b * c   :=  by sorry
