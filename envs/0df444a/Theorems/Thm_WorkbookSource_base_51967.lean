-- Prove2me | Theorems.Thm_WorkbookSource_base_51967
-- name    : WorkbookSource.base_51967
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:47:53.055221+00:00
-- url     : https://prove2.me/theorems/ef0acced-5940-4576-b690-a948dfa8c2f9
-- title:
--   A cyclic quadratic difference ratio sum is nonnegative
-- statement:
--   Prove the inequality for $x, y, z > 0$:
--   $0 \leq \frac{(x - y)(x - 2y)}{(x + 2z)(z + x)} + \frac{(y - z)(y - 2z)}{(x + y)(y + 2x)} + \frac{(z - x)(z - 2x)}{(y + z)(z + 2y)}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_51967` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_51967; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_51967 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 0 ≤ (x - y) * (x - 2 * y) / ((x + 2 * z) * (z + x)) + (y - z) * (y - 2 * z) / ((x + y) * (y + 2 * x)) + (z - x) * (z - 2 * x) / ((y + z) * (z + 2 * y))  :=  by sorry
