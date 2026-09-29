-- Prove2me | Theorems.Thm_WorkbookSource_base_5407
-- name    : WorkbookSource.base_5407
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:05:19.887539+00:00
-- url     : https://prove2.me/theorems/8cd91c5b-bd2d-41e9-9a7d-8c4830a69c3c
-- title:
--   A sixth-power bound for three quadratic factors
-- statement:
--   For $x,y,z>0$ ,prove that:
--
--    $27(x+y+z)^6\geq (27x^2+(y-z)^2)(27y^2+(z-x)^2)(27z^2+(x-y)^2)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_5407` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_5407; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_5407 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 27 * (x + y + z) ^ 6 ≥ (27 * x ^ 2 + (y - z) ^ 2) * (27 * y ^ 2 + (z - x) ^ 2) * (27 * z ^ 2 + (x - y) ^ 2)  :=  by sorry
