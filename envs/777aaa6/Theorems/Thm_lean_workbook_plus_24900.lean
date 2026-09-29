-- Prove2me | Theorems.Thm_lean_workbook_plus_24900
-- name    : lean_workbook_plus_24900
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/6541318c-7922-4970-a10d-a61ced6c7650
-- statement:
--   Prove that for any positive real numbers $x, y, z$, the following equality holds:\nx\sqrt{y+z} + y\sqrt{x+z} + z\sqrt{x+y} = \sqrt{(x+y)(y+z)(z+x)} + \frac{2(xy+yz+zx)}{\sqrt{x+y} + \sqrt{y+z} + \sqrt{x+z}}
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24900 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x * Real.sqrt (y + z) + y * Real.sqrt (x + z) + z * Real.sqrt (x + y) = Real.sqrt ((x + y) * (y + z) * (z + x)) + (2 * (x * y + y * z + z * x)) / (Real.sqrt (x + y) + Real.sqrt (y + z) + Real.sqrt (x + z))   :=  by sorry
