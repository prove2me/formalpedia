-- Prove2me | Theorems.Thm_lean_workbook_plus_57742
-- name    : lean_workbook_plus_57742
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/1df9ed15-e7cd-422a-ab03-84c3ffb38c16
-- statement:
--   For all $x,y,z \geqslant 0$ , show that \n $ \left( x^2y+y^2z+z^2x\right) \cdot \left(\frac{1}{(x-y)^2}+\frac{1}{(y-z)^2} +\frac{1}{(z-x)^2}\right) \geqslant \frac45 \left(x+y+z\right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57742 : ∀ x y z : ℝ, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 → (x^2*y + y^2*z + z^2*x) * (1/(x-y)^2 + 1/(y-z)^2 + 1/(z-x)^2) ≥ 4/5 * (x + y + z)   :=  by sorry
