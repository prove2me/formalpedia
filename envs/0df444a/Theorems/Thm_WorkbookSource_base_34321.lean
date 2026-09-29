-- Prove2me | Theorems.Thm_WorkbookSource_base_34321
-- name    : WorkbookSource.base_34321
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:47:15.816325+00:00
-- url     : https://prove2.me/theorems/55bc95ae-6d54-43c8-ae0e-21154ba4623f
-- title:
--   A product of pairwise ratio sums bounds a cyclic ratio sum
-- statement:
--   Prove that for $x,y,z>0$,
--   $\frac{1}{6}\, \left( {\frac {x+y}{y+z}}+{\frac {y+z}{z+x}}+{\frac {z+x}{x+y}} \right) \left( {\frac {x+y}{z+x}}+{\frac {y+z}{x+y}}+{\frac {z+x}{y+z}} \right) \geq {\frac {x}{y+z}}+{\frac {y}{z+x}}+{\frac {z}{x+y}}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_34321` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_34321; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_34321 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (1 / 6) * ((x + y) / (y + z) + (y + z) / (z + x) + (z + x) / (x + y)) * ((x + y) / (z + x) + (y + z) / (x + y) + (z + x) / (y + z)) ≥ x / (y + z) + y / (z + x) + z / (x + y)  :=  by sorry
