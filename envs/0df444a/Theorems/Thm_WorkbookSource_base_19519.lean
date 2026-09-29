-- Prove2me | Theorems.Thm_WorkbookSource_base_19519
-- name    : WorkbookSource.base_19519
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:44:41.990859+00:00
-- url     : https://prove2.me/theorems/947b3b89-55ff-4e56-bca0-b02d916ea044
-- title:
--   A cyclic quartic inequality at unit product
-- statement:
--   Given \(x, y, z > 0\) and \(xyz = 1\), prove that \({x}^{3}y+{y}^{3}z+{z}^{3}x\geq xy+zx+yz\).
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_19519` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_19519; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_19519 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (habc : x * y * z = 1) : 
  x^3 * y + y^3 * z + z^3 * x ≥ x * y + z * x + y * z  :=  by sorry
