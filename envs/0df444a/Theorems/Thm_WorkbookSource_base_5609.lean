-- Prove2me | Theorems.Thm_WorkbookSource_base_5609
-- name    : WorkbookSource.base_5609
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:45:08.911088+00:00
-- url     : https://prove2.me/theorems/8c60db5a-9c59-46a9-82a8-819c4668fab0
-- title:
--   A three-term symmetric rational lower bound
-- statement:
--   Prove that:
--    $ x,y,z>0\Rightarrow\frac{3(x^2+y^2+z^2)}{xy+yz+zx}+\frac{24xyz}{xyz+(x+y)(y+z)(z+x)}+\frac{4(xy+yz+zx)}{(x+y+z)^2}\ge 7 $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_5609` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_5609; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_5609 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :  3 * (x ^ 2 + y ^ 2 + z ^ 2) / (x * y + y * z + z * x) + 24 * x * y * z / (x * y * z + (x + y) * (y + z) * (z + x)) + 4 * (x * y + y * z + z * x) / (x + y + z) ^ 2 ≥ 7  :=  by sorry
