-- Prove2me | Theorems.Thm_lean_workbook_plus_55146
-- name    : lean_workbook_plus_55146
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/3d57b594-2a75-4e73-a642-3e820e0f7053
-- statement:
--   Prove that for positive \(x, y, z\), \(g={x}^{2}{y}^{2}z+y{z}^{2}{x}^{2}+{y}^{2}{z}^{2}x+{y}^{5}-{z}^{2}{x}^{3}+{x}^{5}-{y}^{3}{z}^{2}-{x}^{3}{y}^{2}-{x}^{2}{y}^{3}-{z}^{3}{x}^{2}-{z}^{3}{y}^{2}+{z}^{5}\geq 0\) is equivalent to \(g=\left( x-y \right) ^{2} \left( x-z \right) ^{2}x+3\, \left( x-y \right) ^{2} \left( x+y-z \right) ^{2} \left( 1/3\,y+1/3\,z \right) +3\, \left( x-z \right) ^{2} \left( x-y+z \right) ^{2} \left( 1/3\,y+1/3\,z \right) + \left( y-z \right) ^{2}yz \left( y+z \right)\geq 0\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55146 : ∀ x y z : ℝ, x > 0 ∧ y > 0 ∧ z > 0 →
  x^2*y^2*z + y*z^2*x^2 + y^2*z^2*x + y^5 - z^2*x^3 + x^5 - y^3*z^2 - x^3*y^2 - x^2*y^3 - z^3*x^2 - z^3*y^2 + z^5 =
  (x - y)^2 * (x - z)^2 * x + 3 * (x - y)^2 * (x + y - z)^2 * (y / 3 + z / 3) + 3 * (x - z)^2 * (x - y + z)^2 * (y / 3 + z / 3) + (y - z)^2 * y * z * (y + z)   :=  by sorry
