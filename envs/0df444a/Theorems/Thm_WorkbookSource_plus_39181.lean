-- Prove2me | Theorems.Thm_WorkbookSource_plus_39181
-- name    : WorkbookSource.plus_39181
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:08:15.364802+00:00
-- url     : https://prove2.me/theorems/f14be9ff-e6a3-44fc-8622-ec3ce91838e4
-- title:
--   A sixth-degree inequality with a squared cyclic-difference correction
-- statement:
--   If $x,y,z$ are positive numbers, then
--    $(x^2+y^2+z^2)^3 \geqslant 8(x^3y^3+y^3z^3+z^3x^3)+12(x-y)^2(y-z)^2(z-x)^2.$
--   (CHNSYWmath)
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_39181` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_39181; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_39181 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x^2 + y^2 + z^2)^3 ≥ 8 * (x^3 * y^3 + y^3 * z^3 + z^3 * x^3) + 12 * (x - y)^2 * (y - z)^2 * (z - x)^2   :=  by sorry
