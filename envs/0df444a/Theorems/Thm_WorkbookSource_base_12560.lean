-- Prove2me | Theorems.Thm_WorkbookSource_base_12560
-- name    : WorkbookSource.base_12560
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:43:26.32054+00:00
-- url     : https://prove2.me/theorems/49c380a6-a43a-468b-9655-f400060bcfa9
-- title:
--   A quadratic ratio with a cubic reciprocal correction
-- statement:
--   If $ x,y,z>0 $ prove that:
--    $ \frac{3(x^2+y^2+z^2)}{xy+yz+zx}+\frac{3xyz}{(x^3+y^3+z^3)}\ge 4 $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_12560` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_12560; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_12560 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 3 * (x ^ 2 + y ^ 2 + z ^ 2) / (x * y + y * z + z * x) + 3 * x * y * z / (x ^ 3 + y ^ 3 + z ^ 3) ≥ 4  :=  by sorry
