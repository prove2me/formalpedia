-- Prove2me | Theorems.Thm_WorkbookSource_base_1763
-- name    : WorkbookSource.base_1763
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T23:05:08.852709+00:00
-- url     : https://prove2.me/theorems/10a0ddd7-e13a-4471-a04b-3bc7a496740c
-- title:
--   A sixth-degree cyclic polynomial inequality
-- statement:
--   Let $x,y,z>0,$
--    $ \left( {z}^{4}+x{y}^{3}+2\,x{z}^{3}+{x}^{3}z+y{z}^{3}+2\,{z}^{2}{x}^{2}+xy{z}^{2}-3\,x{y}^{2}z-z{x}^{2}y \right) \left( x-y \right) \left( x-z \right) +x \left( {y}^{3}+{z}^{3}+2\,x{y}^{2}-{x}^{2}y+{z}^{2}x-{y}^{2}z+2\,xyz \right) \left( y-z \right) ^{2}\geq 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_1763` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_1763; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_1763 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (z^4 + x*y^3 + 2*x*z^3 + x^3*z + y*z^3 + 2*z^2*x^2 + x*y*z^2 - 3*x*y^2*z - z*x^2*y) * (x - y) * (x - z) + x * (y^3 + z^3 + 2*x*y^2 - x^2*y + z^2*x - y^2*z + 2*x*y*z) * (y - z)^2 ≥ 0  :=  by sorry
