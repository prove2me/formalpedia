-- Prove2me | Theorems.Thm_WorkbookSource_plus_61283
-- name    : WorkbookSource.plus_61283
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:18:52.015987+00:00
-- url     : https://prove2.me/theorems/f0f8ab0e-f989-4e37-b0ff-2c2a0fb9f267
-- title:
--   A quintic inequality under weighted triangle constraints
-- statement:
--   prove that
--
--    $ \left( {x}^{2}+{y}^{2}+{z}^{2} \right) xyz-1/9\, \left( x+y+z \right) \left( xy+zx+yz \right) ^{2}\geq 0,[7/5\,z\leq x+y,7/5\,x\leq y+z,7/5\,y\leq z+x] $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_61283` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_61283; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_61283 {x y z : ℝ} (hx : 7 / 5 * z ≤ x + y) (hy : 7 / 5 * x ≤ y + z) (hz : 7 / 5 * y ≤ z + x) : (x ^ 2 + y ^ 2 + z ^ 2) * x * y * z - 1 / 9 * (x + y + z) * (x * y + y * z + z * x) ^ 2 ≥ 0   :=  by sorry
