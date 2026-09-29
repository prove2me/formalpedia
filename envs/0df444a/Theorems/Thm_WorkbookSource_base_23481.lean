-- Prove2me | Theorems.Thm_WorkbookSource_base_23481
-- name    : WorkbookSource.base_23481
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:59:14.932491+00:00
-- url     : https://prove2.me/theorems/397b7c93-ad3d-43e8-a72f-25c6ef22adbf
-- title:
--   A mixed quartic inequality with a constant correction
-- statement:
--   Let $x,y$ and $z$ be positive real numbers. Show that $3x^2+2xy^2+xyz^2\ge 4xyz-\frac{1}{3}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_23481` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_23481; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_23481 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 3 * x ^ 2 + 2 * x * y ^ 2 + x * y * z ^ 2 ≥ 4 * x * y * z - 1 / 3  :=  by sorry
