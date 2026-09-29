-- Prove2me | Theorems.Thm_lean_workbook_plus_60997
-- name    : lean_workbook_plus_60997
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/cf4f0626-e37d-4ad0-b14a-9dbb919a6f15
-- statement:
--   Solve the following system of equations on $\mathbb{R}^3$ \n $x^2+y^2+z^2=1$ \n $x+y+2z=\sqrt7$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60997 (x y z : ℝ) (h₁ : x^2 + y^2 + z^2 = 1) (h₂ : x + y + 2*z = Real.sqrt 7) : x = 2/3 ∧ y = 2/3 ∧ z = 1/3   :=  by sorry
