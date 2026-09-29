-- Prove2me | Theorems.Thm_lean_workbook_plus_36817
-- name    : lean_workbook_plus_36817
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/efc814fb-b20a-44a9-be57-7d275859c9b9
-- statement:
--   If we have $u=x^3 y z^2 , x^2 + y^2 + z^2 =1, xyz=1$ then calculate $\frac {du} {dx} $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36817 (x y z : ℝ) (u : ℝ) (h₁ : x^2 + y^2 + z^2 = 1) (h₂ : x*y*z = 1) (h₃ : u = x^3*y*z^2) : du/dx = 3*x^2*y*z^2 + x^3*z^2 - x^3*y^2*z - x^3*y*z^2   :=  by sorry
