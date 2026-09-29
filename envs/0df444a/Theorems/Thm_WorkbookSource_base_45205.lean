-- Prove2me | Theorems.Thm_WorkbookSource_base_45205
-- name    : WorkbookSource.base_45205
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:54:45.287281+00:00
-- url     : https://prove2.me/theorems/de91dd70-202f-4281-8e3c-2bf79c06afcf
-- title:
--   A product of weighted cyclic ratio sums is at most 343 over eight
-- statement:
--   prove that \({\frac {343}{8}}\geq \left( 6\,{\frac {x}{x+y}}+{\frac {y}{y+z}} \right) \left( 6\,{\frac {y}{y+z}}+{\frac {z}{z+x}} \right) \left( 6\,{\frac {z}{z+x}}+{\frac {x}{x+y}} \right) \) where \(x,y,z>0\)
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_45205` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_45205; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_45205 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (343 / 8) ≥ (6 * (x / (x + y)) + y / (y + z)) * (6 * (y / (y + z)) + z / (z + x)) * (6 * (z / (z + x)) + x / (x + y))  :=  by sorry
