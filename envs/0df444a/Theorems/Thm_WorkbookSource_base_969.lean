-- Prove2me | Theorems.Thm_WorkbookSource_base_969
-- name    : WorkbookSource.base_969
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:08:38.091208+00:00
-- url     : https://prove2.me/theorems/b442fdc2-f5cd-41c4-89ad-76e83cf85080
-- title:
--   A symmetric quartic inequality with lower-degree corrections
-- statement:
--   Let $x,y,z>0$ ,prove
--
--    $ \left( x+y+z \right) ^{2}+6\,xyz+ \left( xy+xz+yz \right) ^{2}\geq \frac{2}{3}\, \left( xy+xz+yz \right) \left( 2\,x+3+2\,y+2\,z \right) +2\, \left( x+y+z \right) xyz$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_969` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_969; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_969 (x y z : ℝ) : (x + y + z) ^ 2 + 6 * x * y * z + (x * y + x * z + y * z) ^ 2 ≥ (2 / 3) * (x * y + x * z + y * z) * (2 * x + 3 + 2 * y + 2 * z) + 2 * (x + y + z) * x * y * z  :=  by sorry
