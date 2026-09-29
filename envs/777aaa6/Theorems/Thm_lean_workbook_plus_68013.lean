-- Prove2me | Theorems.Thm_lean_workbook_plus_68013
-- name    : lean_workbook_plus_68013
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/4d62e3bd-09b6-4140-a939-f2194f65f10a
-- statement:
--   for all real $x,y,z$ prove or disprove that \n\n $x^4+y^4+z^4+3(x^2y^2+x^2z^2+y^2z^2)\geq 2(x^3(y+z)+y^3(x+z)+z^3(x+y))$ \n\n $x^4+y^4+z^4+3(x^2y^2+x^2z^2+y^2z^2)-2(x^3(y+z)+y^3(x+z)+z^3(x+y))=$ \n\n $=(x^2+y^2+z^2-xy-xz-yz)^2=\frac{1}{2}((x-y)^4+(y-z)^4+(z-x)^4).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68013 (x y z : ℝ) : x ^ 4 + y ^ 4 + z ^ 4 + 3 * (x ^ 2 * y ^ 2 + x ^ 2 * z ^ 2 + y ^ 2 * z ^ 2) ≥ 2 * (x ^ 3 * (y + z) + y ^ 3 * (x + z) + z ^ 3 * (x + y))   :=  by sorry
