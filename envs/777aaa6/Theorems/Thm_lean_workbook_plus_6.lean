-- Prove2me | Theorems.Thm_lean_workbook_plus_6
-- name    : lean_workbook_plus_6
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/d41311df-d9a5-429e-a0a5-19a187b71fe9
-- statement:
--   $\begin{array}{l}\left( {{x^2} + 1} \right)\left( {{y^2} + 1} \right)\left( {{z^2} + 1} \right) = \sum {{x^2}} + \sum {{x^2}{y^2}} + {x^2}{y^2}{z^2} + 1\\ = {\left( {x + y + z} \right)^2} - 2\left( {xy + yz + zx} \right) + {\left( {xy + yz + zx} \right)^2} - 2xyz\left( {x + y + z} \right) + {x^2}{y^2}{z^2} + 1\\ = \left[ {{{\left( {x + y + z} \right)}^2} - 2xyz\left( {x + y + z} \right) + {x^2}{y^2}{z^2}} \right] + \left[ {{{\left( {xy + yz + zx} \right)}^2} - 2\left( {xy + yz + zx} \right) + 1} \right]\\ = {\left( {x + y + z - xyz} \right)^2} + {\left( {xy + yz + zx - 1} \right)^2}\end{array}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6  (x y z : ℤ) :
  (x^2 + 1) * (y^2 + 1) * (z^2 + 1) =
  (x + y + z)^2 - 2 * (x * y + y * z + z * x) + (x * y + y * z + z * x)^2 - 2 * x * y * z * (x + y + z) + x^2 * y^2 * z^2 + 1   :=  by sorry
