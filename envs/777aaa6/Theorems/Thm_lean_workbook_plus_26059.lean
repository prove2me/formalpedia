-- Prove2me | Theorems.Thm_lean_workbook_plus_26059
-- name    : lean_workbook_plus_26059
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/c90efb98-34ff-45b0-a292-06e4f2912f21
-- statement:
--   Nesbitt's Inequality: For any three positive reals $a$ , $b$ , and $c$ , we have that $$\frac{a}{b+c}+\frac{b}{c+a}+\frac{c}{a+b}\geq\frac{3}{2}.$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26059 {a b c : ℝ} (h : 0 < a ∧ 0 < b ∧ 0 < c) : (a / (b + c) + b / (c + a) + c / (a + b)) ≥ 3 / 2   :=  by sorry
