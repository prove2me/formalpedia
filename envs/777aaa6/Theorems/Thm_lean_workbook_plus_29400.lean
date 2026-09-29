-- Prove2me | Theorems.Thm_lean_workbook_plus_29400
-- name    : lean_workbook_plus_29400
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/f75b9eb6-2f48-46d3-921e-81a0664d6360
-- statement:
--   for all real $x,y,z$ prove or disprove that \n\n $x^4+y^4+z^4+3(x^2y^2+x^2z^2+y^2z^2)\geq 2(x^3(y+z)+y^3(x+z)+z^3(x+y))$\n\nIt is a particular case of the more general inequality \n\n $\sum x^4+r(r+2)\sum y^2z^2 +(1-r^2)xyz\sum x \geq (r+1)\sum yz(y^2+z^2)$ , \n\nwhere $r$ is a real number.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29400 :  ∀ x y z : ℝ, x ^ 4 + y ^ 4 + z ^ 4 + 3 * (x ^ 2 * y ^ 2 + x ^ 2 * z ^ 2 + y ^ 2 * z ^ 2) ≥ 2 * (x ^ 3 * (y + z) + y ^ 3 * (x + z) + z ^ 3 * (x + y))   :=  by sorry
