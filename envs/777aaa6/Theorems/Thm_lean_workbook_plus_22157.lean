-- Prove2me | Theorems.Thm_lean_workbook_plus_22157
-- name    : lean_workbook_plus_22157
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/c0def17b-a92b-44e9-b53c-aababe23dfc9
-- statement:
--   try using the sum of cubes\n\n $x^3+y^3+z^3-3xyz$ \n\n $=(x^3+y^3)+z^3-3xyz$ \n\n $=(x+y)^3-3xy(x+y)+z^3-3xyz$ \n\n $=(x+y)^3+z^3-3xy(x+y+z)$ \n\n $=\left( (x+y)+z\right) \left( (x+y)^2-(x+y)z+z^2\right) -3xy(x+y+z)$ \n\n $=(x+y+z)(x^2+2xy+y^2-xz-yz+z^2-3xy)$ \n\n $=(x+y+z)(x^2+y^2+z^2-xy-yz-zx)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22157  (x y z : ℂ) :
  x^3 + y^3 + z^3 - 3 * x * y * z
  = (x + y + z) * (x^2 + y^2 + z^2 - x * y - x * z - y * z)   :=  by sorry
