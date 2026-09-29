-- Prove2me | Theorems.Thm_lean_workbook_plus_56290
-- name    : lean_workbook_plus_56290
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/fac67eb1-4d74-45df-a3bc-0790afad59d8
-- statement:
--   Is this inequality true?\n\n$$\frac{x}{2x+y+z} + \frac{y}{x+2y+z} + \frac{z}{x+y+2z} \leq \frac{3}{4}$$\nIf $x,y,z>0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56290 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x / (2 * x + y + z) + y / (x + 2 * y + z) + z / (x + y + 2 * z)) ≤ 3 / 4   :=  by sorry
