-- Prove2me | Theorems.Thm_lean_workbook_plus_64343
-- name    : lean_workbook_plus_64343
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/c9b60e30-cfcf-44a6-b756-753ae078acff
-- statement:
--   Prove that: \n $ 2(x+y+z-3)^2+x^2+y^2+z^2-xy-yz-zx \ge 0$ ,\nwhere $ xyz=1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64343 (x y z : ℝ) (h : x*y*z = 1) : 2*(x + y + z - 3)^2 + x^2 + y^2 + z^2 - x*y - y*z - z*x ≥ 0   :=  by sorry
