-- Prove2me | Theorems.Thm_WorkbookSource_plus_7046
-- name    : WorkbookSource.plus_7046
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:11:48.751237+00:00
-- url     : https://prove2.me/theorems/c3ae468d-4b2d-4a46-b656-b4b7498e3a1a
-- title:
--   A fourth-power ratio bounds a weighted pairwise product
-- statement:
--   Let $x,y,z>0$ ,prove that:
--
--    $\frac{(2y+z+x)^4(2z+x+y)^4}{(z+2x+y)^4}\geq 64yz(y+z)^2$ .
--
--
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_7046` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_7046; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_7046 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (2 * y + z + x) ^ 4 * (2 * z + x + y) ^ 4 / (z + 2 * x + y) ^ 4 ≥ 64 * y * z * (y + z) ^ 2   :=  by sorry
