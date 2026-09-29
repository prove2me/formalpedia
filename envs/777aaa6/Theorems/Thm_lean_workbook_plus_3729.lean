-- Prove2me | Theorems.Thm_lean_workbook_plus_3729
-- name    : lean_workbook_plus_3729
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/c3a5d7b4-7a70-47b9-9571-b21c03e9ac18
-- statement:
--   Prove that $\frac{a}{a+b} + \frac{b}{b+c} + \frac{c}{c+a} < 2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3729 : ∀ a b c : ℝ, (a / (a + b) + b / (b + c) + c / (c + a)) < 2   :=  by sorry
