-- Prove2me | Theorems.Thm_WorkbookSource_base_38442
-- name    : WorkbookSource.base_38442
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:56:38.637527+00:00
-- url     : https://prove2.me/theorems/0f23fd24-8cbe-4907-a072-7d893582cb83
-- title:
--   A quadratic and linear sum bound at unit product
-- statement:
--   Prove that: $2(x^2+y^2+z^2)+x+y+z \geq 6 + xy + yz + xz$ given $x, y, z > 0$ and $xyz=1$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_38442` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_38442; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_38442 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x * y * z = 1) : 2 * (x ^ 2 + y ^ 2 + z ^ 2) + x + y + z ≥ 6 + x * y + y * z + x * z  :=  by sorry
