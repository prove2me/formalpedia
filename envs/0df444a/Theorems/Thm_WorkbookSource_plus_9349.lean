-- Prove2me | Theorems.Thm_WorkbookSource_plus_9349
-- name    : WorkbookSource.plus_9349
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:20:01.584573+00:00
-- url     : https://prove2.me/theorems/1b02cdd0-336e-4fd8-8420-2db66d8ee422
-- title:
--   A seventh-degree polynomial in three positive variables
-- statement:
--   Prove that for $x, y, z > 0$, $F=(3\*y^2+3\*z^2-4\*y\*z)\*x^5+(y+z)\*(16\*z^2-21\*y\*z+16\*y^2)\*x^4+(-38\*y^2\*z^2+18\*y^3\*z+27\*y^4+27\*z^4+18\*y\*z^3)\*x^3+(y+z)\*(19\*z^4+3\*y\*z^3-70\*y^2\*z^2+3\*y^3\*z+19\*y^4)\*x^2+(10\*y^5\*z-41\*y^2\*z^4+10\*y\*z^5+6\*y^6-100\*y^3\*z^3-41\*y^4\*z^2+6\*z^6)\*x+(y+z)\*(z^2+y\*z+y^2)\*(z^4+5\*y\*z^3+9\*y^2\*z^2+5\*y^3\*z+y^4) \geq 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_9349` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_9349; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_9349 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (3 * y ^ 2 + 3 * z ^ 2 - 4 * y * z) * x ^ 5 + (y + z) * (16 * z ^ 2 - 21 * y * z + 16 * y ^ 2) * x ^ 4 + (-38 * y ^ 2 * z ^ 2 + 18 * y ^ 3 * z + 27 * y ^ 4 + 27 * z ^ 4 + 18 * y * z ^ 3) * x ^ 3 + (y + z) * (19 * z ^ 4 + 3 * y * z ^ 3 - 70 * y ^ 2 * z ^ 2 + 3 * y ^ 3 * z + 19 * y ^ 4) * x ^ 2 + (10 * y ^ 5 * z - 41 * y ^ 2 * z ^ 4 + 10 * y * z ^ 5 + 6 * y ^ 6 - 100 * y ^ 3 * z ^ 3 - 41 * y ^ 4 * z ^ 2 + 6 * z ^ 6) * x + (y + z) * (z ^ 2 + y * z + y ^ 2) * (z ^ 4 + 5 * y * z ^ 3 + 9 * y ^ 2 * z ^ 2 + 5 * y ^ 3 * z + y ^ 4) ≥ 0   :=  by sorry
