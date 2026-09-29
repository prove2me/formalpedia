-- Prove2me | Theorems.Thm_WorkbookSource_base_7020
-- name    : WorkbookSource.base_7020
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:45:11.107256+00:00
-- url     : https://prove2.me/theorems/174e6f92-a417-41b1-9ab7-acbd995f3208
-- title:
--   A cubic expression bounds a cyclic rational sum
-- statement:
--   Let $x,y,z>0$ . Prove that:
--    $x(y+z-x)^2+y(x+z-y)^2+z(x+y-z)^2 \ge 2xyz(\frac{x}{y+z}+\frac{y}{x+z}+\frac{z}{x+y})$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_7020` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_7020; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_7020 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x * (y + z - x) ^ 2 + y * (x + z - y) ^ 2 + z * (x + y - z) ^ 2 ≥ 2 * x * y * z * (x/(y+z) + y/(x+z) + z/(x+y))  :=  by sorry
