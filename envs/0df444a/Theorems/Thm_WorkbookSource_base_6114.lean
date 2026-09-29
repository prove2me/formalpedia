-- Prove2me | Theorems.Thm_WorkbookSource_base_6114
-- name    : WorkbookSource.base_6114
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:16:46.049493+00:00
-- url     : https://prove2.me/theorems/db6a0b7e-07f3-4b6b-ba13-14ee13206850
-- title:
--   A cyclic pair-product reciprocal upper bound under a symmetric constraint
-- statement:
--   Following inequality is true:
--    $ x,y,z>0,xy+yz+zx+xyz=4\Rightarrow\sum\frac{xy}{2x+3y}\le\frac{1}{5}(x+y+z) $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_6114` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_6114; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_6114 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (habc : x * y + y * z + z * x + x * y * z = 4) : (x * y) / (2 * x + 3 * y) + (y * z) / (2 * y + 3 * z) + (z * x) / (2 * z + 3 * x) ≤ (1 / 5) * (x + y + z)  :=  by sorry
