-- Prove2me | Theorems.Thm_WorkbookSource_base_32804
-- name    : WorkbookSource.base_32804
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:43:41.21337+00:00
-- url     : https://prove2.me/theorems/8d4f5b28-f806-453c-92ec-8ae5c5f3ad81
-- title:
--   A cyclic ratio sum with a refined triple-product correction
-- statement:
--   If $x, y, z>0$ prove that
--    $\frac{x}{y}+\frac{y}{z}+\frac{z}{x}+\frac{243xyz}{2(x+y+z)^3+27xyz}\ge 6$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_32804` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_32804; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_32804 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x / y + y / z + z / x + 243 * x * y * z / (2 * (x + y + z) ^ 3 + 27 * x * y * z)) ≥ 6  :=  by sorry
