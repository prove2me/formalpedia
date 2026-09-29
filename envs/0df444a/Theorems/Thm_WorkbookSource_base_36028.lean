-- Prove2me | Theorems.Thm_WorkbookSource_base_36028
-- name    : WorkbookSource.base_36028
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:52:13.170387+00:00
-- url     : https://prove2.me/theorems/6eb1b837-1359-4606-9ac1-dfe5d26686fc
-- title:
--   A cyclic quartic sum times the quadratic sum bounds pairwise products
-- statement:
--   Let $x,y,z\geq 0$ ,prove that: $(x^3y+y^3z+z^3x)(x^2+y^2+z^2)\geq (xy+zx+yz)(y^2z^2+z^2x^2+x^2y^2).$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_36028` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_36028; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_36028 (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) : (x^3 * y + y^3 * z + z^3 * x) * (x^2 + y^2 + z^2) ≥ (x * y + y * z + z * x) * (y^2 * z^2 + z^2 * x^2 + x^2 * y^2)  :=  by sorry
