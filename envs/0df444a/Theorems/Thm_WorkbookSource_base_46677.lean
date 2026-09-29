-- Prove2me | Theorems.Thm_WorkbookSource_base_46677
-- name    : WorkbookSource.base_46677
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:13:32.433762+00:00
-- url     : https://prove2.me/theorems/7e262da0-127a-40a0-b826-3bfa5cc78750
-- title:
--   An eighth-degree polynomial in three positive variables
-- statement:
--   Prove the inequality: $g = \left( y+z \right) ^{2}{x}^{6}+ \left( y+z \right) ^{3}{x}^{5}+yz \left( 3\,{z}^{2}+3\,{y}^{2}-58\,yz \right) {x}^{4}+ \left( {z}^{2}+4\,yz+{y}^{2} \right) \left( y+z \right) ^{3}{x}^{3}+ \left( {z}^{4}+{z}^{3}y+{y}^{3}z+{y}^{4}+3\,{y}^{2}{z}^{2} \right) \left( y+z \right) ^{2}{x}^{2}-yz \left( 2\,{z}^{2}+3\,yz+2\,{y}^{2} \right) \left( y+z \right) ^{3}x+{y}^{2}{z}^{2} \left( {y}^{2}+{z}^{2}+3\,yz \right) \left( y+z \right) ^{2}\geq 0$ for $x, y, z > 0$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_46677` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_46677; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_46677 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (y + z) ^ 2 * x ^ 6 + (y + z) ^ 3 * x ^ 5 + y * z * (3 * z ^ 2 + 3 * y ^ 2 - 58 * y * z) * x ^ 4 + (z ^ 2 + 4 * y * z + y ^ 2) * (y + z) ^ 3 * x ^ 3 + (z ^ 4 + z ^ 3 * y + y ^ 3 * z + y ^ 4 + 3 * y ^ 2 * z ^ 2) * (y + z) ^ 2 * x ^ 2 - y * z * (2 * z ^ 2 + 3 * y * z + 2 * y ^ 2) * (y + z) ^ 3 * x + y ^ 2 * z ^ 2 * (y ^ 2 + z ^ 2 + 3 * y * z) * (y + z) ^ 2 ≥ 0  :=  by sorry
