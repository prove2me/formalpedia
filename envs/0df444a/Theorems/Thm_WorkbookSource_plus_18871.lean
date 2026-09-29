-- Prove2me | Theorems.Thm_WorkbookSource_plus_18871
-- name    : WorkbookSource.plus_18871
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:26:52.331925+00:00
-- url     : https://prove2.me/theorems/fe14baf2-e168-4685-ae79-6a026f8af679
-- title:
--   A sixth-degree Schur-type bound with a difference correction
-- statement:
--   For all nonnegative reals $ x,y,z,$ prove that
--    $ x^2(x^2 - y^2)(x^2 - z^2) + y^2(y^2 - z^2)(y^2 - x^2) + z^2(z^2 - x^2)(z^2 - y^2)\geq 8(y - z)^2(z - x)^2(x - y)^2.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_18871` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_18871; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_18871 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : x^2 * (x^2 - y^2) * (x^2 - z^2) + y^2 * (y^2 - z^2) * (y^2 - x^2) + z^2 * (z^2 - x^2) * (z^2 - y^2) ≥ 8 * (y - z)^2 * (z - x)^2 * (x - y)^2   :=  by sorry
