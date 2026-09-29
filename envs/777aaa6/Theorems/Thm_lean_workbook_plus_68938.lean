-- Prove2me | Theorems.Thm_lean_workbook_plus_68938
-- name    : lean_workbook_plus_68938
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/75947387-db45-40a2-a4a3-8553725dbf7a
-- statement:
--   A weaker inequality proven by the student:\n$$\frac{a}{b+c} + \frac{b}{c+a} +\frac{c}{a+b} + \frac{25(ab+bc+ca)}{(a+b+c)^2} \geq 5\sqrt{2} \approx 7.071$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68938 : ∀ a b c : ℝ, (a / (b + c) + b / (c + a) + c / (a + b) + (25 * (a * b + b * c + c * a)) / (a + b + c) ^ 2) ≥ 5 * Real.sqrt 2   :=  by sorry
