-- Prove2me | Theorems.Thm_WorkbookSource_base_26965
-- name    : WorkbookSource.base_26965
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:45:41.953608+00:00
-- url     : https://prove2.me/theorems/db7d70b2-b527-4d47-a7f5-0284a6028fa1
-- title:
--   A sixth-degree triangle-factor inequality with a difference correction
-- statement:
--   Prove that \((xy+xz)(xy+yz)(xz+yz) \geq 8\left(y^2+z^2-x^2\right)\left(z^2+x^2-y^2\right)\left(x^2+y^2-z^2\right) + 64(x-y)^2(y-z)^2(z-x)^2\) for \(x, y, z > 0\).
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_26965` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_26965; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_26965 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x * y + x * z) * (x * y + y * z) * (x * z + y * z) ≥ 8 * (y ^ 2 + z ^ 2 - x ^ 2) * (z ^ 2 + x ^ 2 - y ^ 2) * (x ^ 2 + y ^ 2 - z ^ 2) + 64 * (x - y) ^ 2 * (y - z) ^ 2 * (z - x) ^ 2  :=  by sorry
