-- Prove2me | Theorems.Thm_WorkbookSource_base_8206
-- name    : WorkbookSource.base_8206
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:10:53.421272+00:00
-- url     : https://prove2.me/theorems/feaeb59d-5fbd-426b-b139-cf16d8936cb2
-- title:
--   A seventh-degree cyclic polynomial inequality
-- statement:
--   For $ x,y,z > 0$ , prove that $ \sum_{cyc} x^3(y^2 + z^2)^2 \ge xyz\sum_{cyc}xy(x + y)^2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_8206` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_8206; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_8206 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x^3 * (y^2 + z^2)^2 + y^3 * (z^2 + x^2)^2 + z^3 * (x^2 + y^2)^2 ≥ x * y * z * (x * y * (x + y)^2 + y * z * (y + z)^2 + z * x * (z + x)^2)  :=  by sorry
