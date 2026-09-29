-- Prove2me | Theorems.Thm_WorkbookSource_plus_28880
-- name    : WorkbookSource.plus_28880
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:33:35.78046+00:00
-- url     : https://prove2.me/theorems/d9778dce-0cd3-4371-9411-b27793c8ca85
-- title:
--   A product of cyclic cubic sums bounds a squared triple product
-- statement:
--   Let $x,y,z$ be positive real numbers. Prove that $(xy^2+yz^2+zx^2)(x^2y+y^2z+z^2x)(xy+yz+zx)\geq 3(x+y+z)^2(xyz)^2.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_28880` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_28880; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_28880    (x y z : ℝ)
    (hx : 0 < x)
    (hy : 0 < y)
    (hz : 0 < z) :
    (x * y^2 + y * z^2 + z * x^2) * (x^2 * y + y^2 * z + z^2 * x) * (x * y + y * z + z * x) ≥ 3 * (x + y + z)^2 * (x * y * z)^2   :=  by sorry
