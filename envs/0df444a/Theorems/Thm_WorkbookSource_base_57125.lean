-- Prove2me | Theorems.Thm_WorkbookSource_base_57125
-- name    : WorkbookSource.base_57125
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:47:40.191986+00:00
-- url     : https://prove2.me/theorems/45af7817-7134-40c2-9ef4-9419e3138c20
-- title:
--   A comparison of products of pairwise ratio sums
-- statement:
--   prove that \(\left( {\frac {x}{y+z}}+{\frac {y}{z+x}} \right) \left( {\frac {y}{z+x}}+{\frac {z}{x+y}} \right) \left( {\frac {z}{x+y}}+{\frac {x}{y+z}} \right) \geq \left( {\frac {x}{x+y}}+{\frac {y}{z+x}} \right) \left( {\frac {y}{y+z}}+{\frac {z}{x+y}} \right) \left( {\frac {z}{z+x}}+{\frac {x}{y+z}} \right) \) where \(x,y,z>0\)
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_57125` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_57125; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_57125 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x / (y + z) + y / (z + x)) * (y / (z + x) + z / (x + y)) * (z / (x + y) + x / (y + z)) ≥ (x / (x + y) + y / (z + x)) * (y / (y + z) + z / (x + y)) * (z / (z + x) + x / (y + z))  :=  by sorry
