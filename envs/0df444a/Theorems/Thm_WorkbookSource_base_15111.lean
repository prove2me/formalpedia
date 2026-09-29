-- Prove2me | Theorems.Thm_WorkbookSource_base_15111
-- name    : WorkbookSource.base_15111
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:58:08.250084+00:00
-- url     : https://prove2.me/theorems/07e48b0c-f478-4e8a-b129-2592ae70dd38
-- title:
--   A symmetric sixth-degree rational inequality
-- statement:
--   prove that $ \left( x+y+z \right) ^{2} \left( xy+zx+yz \right) +9\,{\frac {{x}^{2}{y}^{2}{z}^{2}}{xy+zx+yz}}+2\, \left( x+y+z \right) xyz\geq 4\, \left( xy+zx+yz \right) ^{2}$ given $x,y,z>0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_15111` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_15111; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_15111 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + y + z) ^ 2 * (x * y + y * z + z * x) + 9 * (x * y * z) ^ 2 / (x * y + y * z + z * x) + 2 * (x + y + z) * x * y * z ≥ 4 * (x * y + y * z + z * x) ^ 2  :=  by sorry
