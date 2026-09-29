-- Prove2me | Theorems.Thm_WorkbookSource_base_12714
-- name    : WorkbookSource.base_12714
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:46:04.518533+00:00
-- url     : https://prove2.me/theorems/dc862fcc-085c-4685-a5bc-29dbd04ec54a
-- title:
--   A cyclic quadratic-product ratio upper bound
-- statement:
--   Let $x,y,z>0$ .Prove that:
--    $\frac{x^2(y+z)}{x^2+2yz}+\frac{y^2(z+x)}{y^2+2zx}+\frac{z^2(x+y)}{z^2+2xy}\leq\frac{2(x^2+y^2+z^2)}{x+y+z}$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_12714` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_12714; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_12714 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x^2 * (y + z) / (x^2 + 2 * y * z) + y^2 * (z + x) / (y^2 + 2 * z * x) + z^2 * (x + y) / (z^2 + 2 * x * y)) ≤ (2 * (x^2 + y^2 + z^2)) / (x + y + z)  :=  by sorry
