-- Prove2me | Theorems.Thm_lean_workbook_plus_27794
-- name    : lean_workbook_plus_27794
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/ff67eba1-3434-4851-b493-75fc5ec37815
-- statement:
--   prove that \n\n $\left( x+y+z \right) \left( -2\, \left( x+y+z \right) xyz+ \left( xy+zx+yz \right) ^{2} \right) -2\, \left( xy+zx+yz \right) xyz\geq {x}^{2}{z}^{3}+{x}^{3}{y}^{2}+{y}^{3}{z}^{2}$\n\n$x,y,z>0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27794 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + y + z) * (-(2 * (x + y + z) * x * y * z) + (x * y + y * z + z * x) ^ 2) - 2 * (x * y + y * z + z * x) * x * y * z ≥ x ^ 2 * z ^ 3 + x ^ 3 * y ^ 2 + y ^ 3 * z ^ 2   :=  by sorry
