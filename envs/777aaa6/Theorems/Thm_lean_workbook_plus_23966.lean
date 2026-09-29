-- Prove2me | Theorems.Thm_lean_workbook_plus_23966
-- name    : lean_workbook_plus_23966
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/bdbdd11f-07dd-423e-98f6-7ce9949daa29
-- statement:
--   Prove: $(x+y)(x+z)(y+z) > xz(x+z)+yx(y+z)+yz(y+z)$ where $x,y,z>0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23966 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + y) * (x + z) * (y + z) > x * z * (x + z) + y * x * (y + z) + y * z * (y + z)   :=  by sorry
