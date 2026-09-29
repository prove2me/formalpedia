-- Prove2me | Theorems.Thm_lean_workbook_plus_73842
-- name    : lean_workbook_plus_73842
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/b25c917d-21e3-4250-8a0a-1c021b2b2b4d
-- statement:
--   If $x,y,z>0$ , then $\frac{1}{x+y}+\frac{1}{y+z}+\frac{1}{z+x}\le \frac{3\left( x+y+z \right)}{2\left( xy+yz+zx \right)}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73842 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) ≤ (3 * (x + y + z)) / (2 * (x*y + y*z + z*x))   :=  by sorry
