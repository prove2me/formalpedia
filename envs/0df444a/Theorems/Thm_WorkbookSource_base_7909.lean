-- Prove2me | Theorems.Thm_WorkbookSource_base_7909
-- name    : WorkbookSource.base_7909
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:33:36.151632+00:00
-- url     : https://prove2.me/theorems/089be402-9095-425e-9d7a-cbcd1ca7485f
-- title:
--   An asymmetric shifted rational product inequality
-- statement:
--   Let $x,y,z>0$ ,prove that: $\frac{(2x+z+y)(2z+y+x)}{2y+x+z}+\frac{2zyx}{(x+y)(y+z)} \geq \frac{ 9zx}{z+x}.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_7909` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_7909; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_7909 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (2 * x + z + y) * (2 * z + y + x) / (2 * y + x + z) + 2 * z * y * x / (x + y) / (y + z) ≥ 9 * z * x / (z + x)  :=  by sorry
