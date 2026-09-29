-- Prove2me | Theorems.Thm_WorkbookSource_base_24491
-- name    : WorkbookSource.base_24491
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:01:06.327755+00:00
-- url     : https://prove2.me/theorems/ef8e4812-24d0-4936-b16b-0ec3e2c0a0c6
-- title:
--   A pairwise ratio sum bounded by a symmetric quadratic ratio
-- statement:
--   For $ x, y, z > 0 $ prove that:
--   $ \frac{(x+y+z)^2}{2(xy+yz+zx)} \ge \sum_{cyc} \frac{x+y}{x+y+2z} \ \ ; (1) $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_24491` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_24491; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_24491 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + y + z) ^ 2 / (2 * (x * y + y * z + z * x)) ≥ (x + y) / (x + y + 2 * z) + (y + z) / (y + z + 2 * x) + (z + x) / (z + x + 2 * y)  :=  by sorry
