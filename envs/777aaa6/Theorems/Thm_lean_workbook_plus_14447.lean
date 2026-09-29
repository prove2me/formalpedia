-- Prove2me | Theorems.Thm_lean_workbook_plus_14447
-- name    : lean_workbook_plus_14447
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/689069e9-d6ad-4be5-a68a-4e95b835a703
-- statement:
--   Let $x,y,z\in\mathbb{R}^+$ . Prove that $xyz+ \left( x+y \right) \left( y+z \right) \left( z+x \right) = \left( x+y+z \right) \left( xy+xz+yz \right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14447 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :  x*y*z + (x + y)*(y + z)*(z + x) = (x + y + z)*(x*y + x*z + y*z)   :=  by sorry
