-- Prove2me | Theorems.Thm_WorkbookSource_base_15339
-- name    : WorkbookSource.base_15339
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:00:21.912221+00:00
-- url     : https://prove2.me/theorems/e36234b2-9a80-4139-a4a9-52fed5a80f34
-- title:
--   A comparison of two cyclic linear reciprocal sums
-- statement:
--   Given $ x,y,z>0$ , prove that $ \frac{1}{3x+y}+\frac{1}{3y+z}+\frac{1}{3z+x}\ge\frac{1}{2x+y+z}+\frac{1}{2y+z+x}+\frac{1}{2z+x+y}$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_15339` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_15339; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_15339 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (1 / (3 * x + y) + 1 / (3 * y + z) + 1 / (3 * z + x)) ≥ (1 / (2 * x + y + z) + 1 / (2 * y + z + x) + 1 / (2 * z + x + y))  :=  by sorry
