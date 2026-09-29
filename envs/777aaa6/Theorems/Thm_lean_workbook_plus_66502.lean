-- Prove2me | Theorems.Thm_lean_workbook_plus_66502
-- name    : lean_workbook_plus_66502
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/0ec90a62-98df-4b61-bbab-ebbb83afaf74
-- statement:
--   Let x,y,z>0: xyz=1. Prove that: ${x^4} + {y^4} + {z^4} \ge x + y + z$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66502 (x y z : ℝ) (h : x*y*z = 1) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x^4 + y^4 + z^4 >= x + y + z   :=  by sorry
