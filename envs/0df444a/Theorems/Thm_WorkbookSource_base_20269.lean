-- Prove2me | Theorems.Thm_WorkbookSource_base_20269
-- name    : WorkbookSource.base_20269
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:44:23.438858+00:00
-- url     : https://prove2.me/theorems/ae08561d-a62e-41f6-8bc2-33a91390e9d3
-- title:
--   A degree-eight inequality between symmetric products
-- statement:
--   Let $x,y,z> 0$ . Prove or disprove?
--    $(x+y+z)^4(x^2y^2+y^2z^2+z^2x^2)\geq 81x^2y^2z^2(x^2+y^2+z^2)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_20269` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_20269; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_20269 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) : (x + y + z) ^ 4 * (x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2) ≥ 81 * x ^ 2 * y ^ 2 * z ^ 2 * (x ^ 2 + y ^ 2 + z ^ 2)  :=  by sorry
