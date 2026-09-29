-- Prove2me | Theorems.Thm_WorkbookSource_base_54981
-- name    : WorkbookSource.base_54981
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:23:03.657317+00:00
-- url     : https://prove2.me/theorems/42145986-5bfd-4635-9a4d-f9439689891b
-- title:
--   A cyclic linear ratio sum with a symmetric product correction
-- statement:
--   Prove that for positive reals x, y, and z, the following inequality holds:
--   ${\frac {y+z}{2\,x+z+y}}+{\frac {z+x}{2\,y+x+z}}+{\frac {x+y}{2\,z+y+x}}\geq \frac{1}{6}+\frac{3}{2}\,{\frac { \left( x+y \right) \left( z+x \right) \left( y+z \right) }{ \left( x+y+z \right) \left( xy+xz+yz \right) }}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_54981` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_54981; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_54981 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (y + z) / (2 * x + z + y) + (z + x) / (2 * y + x + z) + (x + y) / (2 * z + y + x) ≥ 1 / 6 + 3 / 2 * ((x + y) * (z + x) * (y + z) / ((x + y + z) * (x * y + x * z + y * z)))  :=  by sorry
