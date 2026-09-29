-- Prove2me | Theorems.Thm_WorkbookSource_base_13913
-- name    : WorkbookSource.base_13913
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:51:51.851136+00:00
-- url     : https://prove2.me/theorems/5d99078b-2776-400f-9e80-e91a3b69f4c1
-- title:
--   A symmetric rational product bounds a reciprocal sum
-- statement:
--   Prove that for positive reals x, y, and z, the following inequality holds:
--   $\frac{9}{2}\,{\frac { \left( x+y \right) \left( z+x \right) \left( y+z \right) }{ \left( x+y+z \right) \left( xy+xz+yz \right) }}\geq {\frac {y+z}{2\,x+z+y}}+{\frac {z+x}{2\,y+x+z}}+{\frac {x+y}{2\,z+y+x}}+\frac{5}{2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_13913` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_13913; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_13913 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (9 / 2 * (x + y) * (z + x) * (y + z) / ((x + y + z) * (x * y + x * z + y * z))) ≥ (y + z) / (2 * x + z + y) + (z + x) / (2 * y + x + z) + (x + y) / (2 * z + y + x) + 5 / 2  :=  by sorry
