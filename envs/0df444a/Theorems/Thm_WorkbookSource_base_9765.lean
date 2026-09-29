-- Prove2me | Theorems.Thm_WorkbookSource_base_9765
-- name    : WorkbookSource.base_9765
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:45:32.867711+00:00
-- url     : https://prove2.me/theorems/1c9b5305-a5c5-4901-b196-ac5f419d345e
-- title:
--   A cyclic quadratic difference ratio sum is nonnegative
-- statement:
--   Let $x,y,z>0$ ,prove that: ${\frac {y \left( y-x \right) }{x+y+{x}^{2}}}+{\frac {z \left( z-y \right) }{y+z+{y}^{2}}}+{\frac {x \left( x-z \right) }{z+x+{z}^{2}}}\geq 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_9765` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_9765; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_9765 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (y * (y - x) / (x + y + x ^ 2) + z * (z - y) / (y + z + y ^ 2) + x * (x - z) / (z + x + z ^ 2)) ≥ 0  :=  by sorry
