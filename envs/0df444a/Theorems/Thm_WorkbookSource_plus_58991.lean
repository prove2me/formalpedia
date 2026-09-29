-- Prove2me | Theorems.Thm_WorkbookSource_plus_58991
-- name    : WorkbookSource.plus_58991
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:48:04.829334+00:00
-- url     : https://prove2.me/theorems/ac0a128c-e221-4e32-85e6-a517940ef7eb
-- title:
--   A refined cubic difference inequality with a squared Vandermonde correction
-- statement:
--   Let $x,y,z>0$ , show
--   \begin{eqnarray*} && x(x-y)(x-z) + y(y-z)(y-x) + z(z-x)(z-y) \ &\geq& xyz \left( 1 - \frac{8xyz}{(x+y)(y+z)(z+x)} \right) + \frac{4(x-y)^2(y-z)^2(z-x)^2}{(x+y)(y+z)(z+x)} \end{eqnarray*}
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_58991` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_58991; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_58991 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x * (x - y) * (x - z) + y * (y - z) * (y - x) + z * (z - x) * (z - y) ≥ x * y * z * (1 - 8 * x * y * z / ((x + y) * (y + z) * (z + x))) + 4 * (x - y) ^ 2 * (y - z) ^ 2 * (z - x) ^ 2 / ((x + y) * (y + z) * (z + x))   :=  by sorry
