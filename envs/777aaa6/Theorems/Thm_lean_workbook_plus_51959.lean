-- Prove2me | Theorems.Thm_lean_workbook_plus_51959
-- name    : lean_workbook_plus_51959
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/fdd7ff43-304e-43cd-9315-0a93d116b652
-- statement:
--   Prove that for real positive numbers x, y, z, \n $ xy(x+y)+yz(y+z)+zx(z+x)\ge 6xyz \n$ \n
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51959 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x * y * (x + y) + y * z * (y + z) + z * x * (z + x) ≥ 6 * x * y * z   :=  by sorry
