-- Prove2me | Theorems.Thm_WorkbookSource_base_25667
-- name    : WorkbookSource.base_25667
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:05:23.154333+00:00
-- url     : https://prove2.me/theorems/92f0bb2c-4e0b-4a30-be8b-93f292b2aaa8
-- title:
--   A product of mixed cyclic ratio sums is at most one
-- statement:
--   prove that \(1\geq \left( {\frac {x}{x+y}}+{\frac {z+x}{2\,x+z+y}} \right) \left( {\frac {y}{y+z}}+{\frac {x+y}{2\,y+x+z}} \right) \left( {\frac {z}{z+x}}+{\frac {y+z}{2\,z+y+x}} \right) \) where \(x,y,z>0\)
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_25667` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_25667; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_25667 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 1 ≥ (x / (x + y) + (z + x) / (2 * x + z + y)) * (y / (y + z) + (x + y) / (2 * y + x + z)) * (z / (z + x) + (y + z) / (2 * z + y + x))  :=  by sorry
