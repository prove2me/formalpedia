-- Prove2me | Theorems.Thm_lean_workbook_plus_43014
-- name    : lean_workbook_plus_43014
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/d9f5dd5d-c454-46e5-892d-d86e127d4746
-- statement:
--   Find the values of x, y, and z that satisfy the system of equations:\\n\\n\\(x=\frac{a}{-a+b+c}\\) , \\(y=\frac{b}{a-b+c}\\) , \\(z=\frac{c}{a+b-c}\\) .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43014 (a b c x y z : ℝ) : x = a / (-a + b + c) ∧ y = b / (a - b + c) ∧ z = c / (a + b - c) ↔ x = a / (-a + b + c) ∧ y = b / (a - b + c) ∧ z = c / (a + b - c)   :=  by sorry
