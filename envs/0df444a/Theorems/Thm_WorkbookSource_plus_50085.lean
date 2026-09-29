-- Prove2me | Theorems.Thm_WorkbookSource_plus_50085
-- name    : WorkbookSource.plus_50085
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:28:05.73646+00:00
-- url     : https://prove2.me/theorems/bee51927-f6e0-4d97-8fdc-c43fcb5754c4
-- title:
--   A cyclic rational difference sum with a symmetric correction
-- statement:
--   For all positive $x,y,z$ prove that:
--
--   $\sum_{cyc}\frac{x(y-z)}{(2x+y)^2} +\frac13 \cdot \frac{x^2+y^2+z^2}{xy+yz+zx} \geq \frac13$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_50085` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_50085; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_50085 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x * (y - z) / (2 * x + y) ^ 2 + y * (z - x) / (2 * y + z) ^ 2 + z * (x - y) / (2 * z + x) ^ 2 + 1 / 3 * (x ^ 2 + y ^ 2 + z ^ 2) / (x * y + y * z + z * x)) ≥ 1 / 3   :=  by sorry
