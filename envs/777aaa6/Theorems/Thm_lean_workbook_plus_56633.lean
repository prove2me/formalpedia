-- Prove2me | Theorems.Thm_lean_workbook_plus_56633
-- name    : lean_workbook_plus_56633
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/f977e775-8692-4bfa-8496-6479d9fada10
-- statement:
--   For non-negatives $a$ , $b$ and $c$ such that $ab+ac+bc=3$ prove that: $ 1\geq\frac{a}{a+2}+\frac{b}{b+2}+\frac{c}{c+2} $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56633 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a * b + b * c + c * a = 3) : 1 ≥ a / (a + 2) + b / (b + 2) + c / (c + 2)   :=  by sorry
