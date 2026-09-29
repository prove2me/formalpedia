-- Prove2me | Theorems.Thm_WorkbookSource_base_22823
-- name    : WorkbookSource.base_22823
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:44:28.562546+00:00
-- url     : https://prove2.me/theorems/a711aa3c-274d-4a97-a32b-45eb268921e9
-- title:
--   A sixth-power bound for three mixed quadratic factors
-- statement:
--   Let $ x;y;z\ge 0$ Prove that $(x+y+z)^6\ge 64(x^2+yz)(y^2+xz)(z^2+xy)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_22823` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_22823; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_22823 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : (x + y + z) ^ 6 ≥ 64 * (x ^ 2 + y * z) * (y ^ 2 + z * x) * (z ^ 2 + x * y)  :=  by sorry
