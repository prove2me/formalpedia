-- Prove2me | Theorems.Thm_lean_workbook_plus_77846
-- name    : lean_workbook_plus_77846
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/6650bcca-970b-4db1-a272-f15deb53eb1d
-- statement:
--   A parabola in $y=ax^2+bx+c$ form passes through the points $(0,-2)$ , $(4,0)$ , and $(6,-2)$ . Determine $a+b+c$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77846 (a b c : ℝ) (h₁ : a * 0 ^ 2 + b * 0 + c = -2) (h₂ : a * 4 ^ 2 + b * 4 + c = 0) (h₃ : a * 6 ^ 2 + b * 6 + c = -2) : a + b + c = -3 / 4   :=  by sorry
