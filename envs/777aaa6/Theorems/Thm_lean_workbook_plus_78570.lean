-- Prove2me | Theorems.Thm_lean_workbook_plus_78570
-- name    : lean_workbook_plus_78570
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/cbc2cb40-c843-4d95-be21-10f400600841
-- statement:
--   prove \n\n $\left( -{y}^{2}{z}^{2}+ \left( y+z \right) ^{3}x \right) \left( y-z \right) ^{2}+ \left( -{z}^{2}{x}^{2}+ \left( z+x \right) ^{3}y \right) \left( z-x \right) ^{2}+ \left( -{x}^{2}{y}^{2}+ \left( x+y \right) ^{3}z \right) \left( x-y \right) ^{2}\geq \left( 3+2\,\sqrt {2} \right) \left( x-y \right) ^{2} \left( y-z \right) ^{2} \left( z-x \right) ^{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78570 : ∀ x y z : ℝ, (-x^2*y^2 + (x + y)^3*z)*(x - y)^2 + (-y^2*z^2 + (y + z)^3*x)*(y - z)^2 + (-z^2*x^2 + (z + x)^3*y)*(z - x)^2 ≥ (3 + 2*Real.sqrt 2)*(x - y)^2*(y - z)^2*(z - x)^2   :=  by sorry
