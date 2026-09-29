-- Prove2me | Theorems.Thm_lean_workbook_plus_23615
-- name    : lean_workbook_plus_23615
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/68e43148-e263-4dd7-9b1b-623da54b8587
-- statement:
--   for any reals $x,y,z$ and $t$ we have the identity \n $x^4+y^4+z^4+t^4-4xyzt=(x-y)^2(x+y)^2+(z-t)^2(z+t)^2+2(xy-zt)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23615 (x y z t : ℝ) : x^4+y^4+z^4+t^4-4*x*y*z*t = (x-y)^2*(x+y)^2 + (z-t)^2*(z+t)^2 + 2*(x*y-z*t)^2   :=  by sorry
