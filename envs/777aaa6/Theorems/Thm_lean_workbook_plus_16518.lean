-- Prove2me | Theorems.Thm_lean_workbook_plus_16518
-- name    : lean_workbook_plus_16518
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/b61fbba6-f560-4c28-ae13-d6e14c7f568d
-- statement:
--   Prove that $(x^2y^2+y^2z^2+z^2x^2)^2\geq 3x^2y^2z^2(xy+yz+zx)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16518 (x y z : ℝ) :
  (x^2*y^2+y^2*z^2+z^2*x^2)^2 ≥ 3*x^2*y^2*z^2*(x*y+y*z+z*x)   :=  by sorry
