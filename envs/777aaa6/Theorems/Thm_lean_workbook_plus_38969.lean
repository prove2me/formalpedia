-- Prove2me | Theorems.Thm_lean_workbook_plus_38969
-- name    : lean_workbook_plus_38969
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/edc5cc7d-0eb8-43cd-8f4e-afce4681b154
-- statement:
--   Let $x,y,z,t>0$ , prove: $(x+y+z+t)^3 \ge 16(xyz+yzt+ztx+txy)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38969 (x y z t : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (ht : 0 < t) : (x + y + z + t) ^ 3 ≥ 16 * (x*y*z + y*z*t + z*t*x + t*x*y)   :=  by sorry
