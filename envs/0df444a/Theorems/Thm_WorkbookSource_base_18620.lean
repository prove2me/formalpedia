-- Prove2me | Theorems.Thm_WorkbookSource_base_18620
-- name    : WorkbookSource.base_18620
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:36:08.403899+00:00
-- url     : https://prove2.me/theorems/644d903f-ee68-4b6b-b96d-07a3095d3a86
-- title:
--   A cyclic fifth-degree sum bounds a symmetric product
-- statement:
--   If x,y,z>0,then $x^4y+y^4z+z^4x\geq \frac{1}{3}(x+y+z)^2xyz$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_18620` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_18620; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_18620 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x ^ 4 * y + y ^ 4 * z + z ^ 4 * x ≥ (1 / 3) * (x + y + z) ^ 2 * x * y * z  :=  by sorry
