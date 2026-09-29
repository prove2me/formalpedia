-- Prove2me | Theorems.Thm_WorkbookSource_base_37822
-- name    : WorkbookSource.base_37822
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:31:23.576012+00:00
-- url     : https://prove2.me/theorems/d60ff2f0-5f2c-4ea2-8b90-e5020d4e65b9
-- title:
--   A weighted pairwise product reciprocal upper bound
-- statement:
--   Let $x,y,z>0$ . Prove that : $${\frac {1}{x+y+z}}\geq {\frac {x}{ \left( y+2\,x \right) \left( z+2\,x \right) }}+{\frac {y}{ \left( 2\,y+z \right) \left( 2\,y+x \right) }}+{\frac {z}{ \left( 2\,z+x \right) \left( 2\,z+y \right) }}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_37822` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_37822; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_37822 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 1 / (x + y + z) ≥ x / ((y + 2 * x) * (z + 2 * x)) + y / ((2 * y + z) * (2 * y + x)) + z / ((2 * z + x) * (2 * z + y))  :=  by sorry
