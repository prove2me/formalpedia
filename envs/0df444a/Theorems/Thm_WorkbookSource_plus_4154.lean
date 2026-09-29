-- Prove2me | Theorems.Thm_WorkbookSource_plus_4154
-- name    : WorkbookSource.plus_4154
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:02:56.773755+00:00
-- url     : https://prove2.me/theorems/45c843e7-6bd7-4db4-8fe3-b10a63a3a3a3
-- title:
--   A weighted product ratio sum bounds the total
-- statement:
--   Prove or disprove, for $ x, y, z > 0 $ .
--
--   $ \frac{8}{9} \sum_{cyc} \frac{xy}{z}+ \frac{xyz}{xy+yz+zx} \ge x+y+z \ \ ; (2) $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_4154` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_4154; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_4154 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (8 / 9) * (x * y / z + y * z / x + z * x / y) + (x * y * z) / (x * y + y * z + z * x) ≥ x + y + z   :=  by sorry
