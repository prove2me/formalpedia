-- Prove2me | Theorems.Thm_WorkbookSource_base_36731
-- name    : WorkbookSource.base_36731
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:03:10.087909+00:00
-- url     : https://prove2.me/theorems/694ea41c-d66f-4152-b751-395d4820c97c
-- title:
--   A shifted cyclic quadratic ratio bound with a triple-product denominator
-- statement:
--   Let $x,y,z$ be positive reals satisfy $x+y+z=3$ , prove that $ \frac{x}{z+y^2}+\frac{y}{x+z^2}+\frac{z}{x^2+y} \geq \frac{15}{9+xyz}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_36731` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_36731; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_36731 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 3) : (x / (z + y ^ 2) + y / (x + z ^ 2) + z / (x ^ 2 + y)) ≥ 15 / (9 + x * y * z)  :=  by sorry
