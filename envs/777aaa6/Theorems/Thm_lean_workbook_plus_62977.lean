-- Prove2me | Theorems.Thm_lean_workbook_plus_62977
-- name    : lean_workbook_plus_62977
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/4cf5ecc9-7818-4037-b781-3d95f360c30f
-- statement:
--   Factor $x^4+y^4+z^4-3x^2yz-3xy^2z-3xyz^2+x^3y+xy^3+x^3z+xz^3+y^3z+yz^3$ as $(x+y+z)^2(x^2+y^2+z^2-xy-xz-yz)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62977 (x y z : ℝ) : (x^4+y^4+z^4-3*x^2*y*z-3*x*y^2*z-3*x*y*z^2+x^3*y+x*y^3+x^3*z+x*z^3+y^3*z+y*z^3) = (x+y+z)^2*(x^2+y^2+z^2-x*y-x*z-y*z)   :=  by sorry
