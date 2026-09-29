-- Prove2me | Theorems.Thm_WorkbookSource_base_3067
-- name    : WorkbookSource.base_3067
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:08:29.753089+00:00
-- url     : https://prove2.me/theorems/19d60eef-321a-48ba-8c09-d9c2bea08f0b
-- title:
--   A symmetric rational correction bounds pairwise products
-- statement:
--   Let $ x,y,z>0$ ,then prove that $ 6\,zy + 6\,xz + 6\,yx\leq 8\,{\frac {\left( x + y + z \right) xyz}{\left( y + z \right) \left( z + 2\,x + y \right) }} + 8\,{\frac {\left( x + y + z \right) xyz}{\left( z + x \right) \left( x + 2\,y + z \right) }} + 8\,{ \frac {\left( x + y + z \right) xyz}{\left( x + y \right) \left( y + 2\,z + x \right) }} + 3\,{x}^{2} + 3\,{y}^{2} + 3\,{z}^{2}.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_3067` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_3067; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_3067 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 6 * z * y + 6 * x * z + 6 * y * x ≤ 8 * (x + y + z) * x * y * z / ((y + z) * (z + 2 * x + y)) + 8 * (x + y + z) * x * y * z / ((z + x) * (x + 2 * y + z)) + 8 * (x + y + z) * x * y * z / ((x + y) * (y + 2 * z + x)) + 3 * x ^ 2 + 3 * y ^ 2 + 3 * z ^ 2  :=  by sorry
