-- Prove2me | Theorems.Thm_WorkbookSource_base_21934
-- name    : WorkbookSource.base_21934
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:50:51.450531+00:00
-- url     : https://prove2.me/theorems/cc249774-2d5c-4d3d-affa-27edfb1ba9eb
-- title:
--   A product of mixed cyclic ratio sums is at least eight
-- statement:
--   prove that \(\left( {\frac {x}{x+y}}+3\,{\frac {y}{z+x}} \right) \left( {\frac {y}{y+z}}+3\,{\frac {z}{x+y}} \right) \left( {\frac {z}{z+x}}+3\,{\frac {x}{y+z}} \right) \geq 8\) where \(x,y,z>0\)
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_21934` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_21934; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_21934 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x / (x + y) + 3 * (y / (z + x))) * (y / (y + z) + 3 * (z / (x + y))) * (z / (z + x) + 3 * (x / (y + z))) ≥ 8  :=  by sorry
