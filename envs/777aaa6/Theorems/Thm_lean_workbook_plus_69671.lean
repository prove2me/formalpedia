-- Prove2me | Theorems.Thm_lean_workbook_plus_69671
-- name    : lean_workbook_plus_69671
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/fbc8e9b1-1cb4-45d3-ab20-dea01a961fbb
-- statement:
--   If $x,y,z$ are real numbers, then \n\n $x^4+y^4+z^4+(xy+yz+zx)(x^2+y^2+z^2)\ge4xyz(x+y+z).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69671 (x y z : ℝ) : x^4 + y^4 + z^4 + (x*y + y*z + z*x)*(x^2 + y^2 + z^2) ≥ 4*x*y*z*(x + y + z)   :=  by sorry
