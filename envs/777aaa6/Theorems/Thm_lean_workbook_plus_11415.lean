-- Prove2me | Theorems.Thm_lean_workbook_plus_11415
-- name    : lean_workbook_plus_11415
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/ee56cf42-5d4d-4f41-b9fc-8503a64b89db
-- statement:
--   For positive reals $ x,y,z$ prove that $ \sum \frac {2}{x + y} \ge \frac{9}{x+y+z}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11415 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (2 / (x + y) + 2 / (y + z) + 2 / (z + x)) ≥ 9 / (x + y + z)   :=  by sorry
