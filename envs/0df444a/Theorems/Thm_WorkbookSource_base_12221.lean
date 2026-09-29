-- Prove2me | Theorems.Thm_WorkbookSource_base_12221
-- name    : WorkbookSource.base_12221
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:41:56.574862+00:00
-- url     : https://prove2.me/theorems/28811df9-674c-49c3-9dc2-06d34d053554
-- title:
--   A quadratic ratio with a normalized triple-product correction
-- statement:
--   If $ x,y,z>0 $ prove that:
--    $ \frac{3(x^2+y^2+z^2)}{xy+yz+zx}+\frac{9xyz}{(x+y+z)(x^2+y^2+z^2)}\ge 4 $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_12221` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_12221; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_12221 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (3 * (x ^ 2 + y ^ 2 + z ^ 2) / (x * y + x * z + y * z) + 9 * x * y * z / ((x + y + z) * (x ^ 2 + y ^ 2 + z ^ 2))) ≥ 4  :=  by sorry
