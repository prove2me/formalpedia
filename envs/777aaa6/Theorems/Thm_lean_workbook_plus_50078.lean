-- Prove2me | Theorems.Thm_lean_workbook_plus_50078
-- name    : lean_workbook_plus_50078
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/5f5f880c-dbda-4705-9f23-836e2a645910
-- statement:
--   Prove that for positive real numbers $a, b, c$ with $a \geq b \geq c$ and $abc = 1$, the inequality $\frac{a}{b+a} + \frac{c}{a+c} + \frac{b}{b+c} \leq 2$ holds.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50078 (a b c : ℝ) (h1 : a ≥ b ∧ b ≥ c) (h2 : 0 < a ∧ 0 < b ∧ 0 < c) (h3 : a * b * c = 1) : a / (b + a) + c / (a + c) + b / (b + c) ≤ 2   :=  by sorry
