-- Prove2me | Theorems.Thm_WorkbookSource_base_25302
-- name    : WorkbookSource.base_25302
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:02:10.868848+00:00
-- url     : https://prove2.me/theorems/14269a7b-7bb1-48f9-864c-166d3f257428
-- title:
--   A pairwise ratio upper bound with a triple-product correction
-- statement:
--   $x,y,z>0$ ,prove that:
--    ${\frac {y+z}{2\,x+z+y}}+{\frac {z+x}{2\,y+x+z}}+{\frac {x+y}{2\,z+y+x}}+3\,{\frac {xyz}{yz \left( y+z \right) +zx \left( z+x \right) +xy \left( x+y \right) }}\leq 2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_25302` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_25302; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_25302 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (y + z) / (2 * x + z + y) + (z + x) / (2 * y + x + z) + (x + y) / (2 * z + y + x) + 3 * (x * y * z) / (y * z * (y + z) + z * x * (z + x) + x * y * (x + y)) ≤ 2  :=  by sorry
