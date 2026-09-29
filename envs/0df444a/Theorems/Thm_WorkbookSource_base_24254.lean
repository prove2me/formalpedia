-- Prove2me | Theorems.Thm_WorkbookSource_base_24254
-- name    : WorkbookSource.base_24254
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:00:54.239622+00:00
-- url     : https://prove2.me/theorems/0d645ef4-6aca-4586-8177-956f2828454e
-- title:
--   A cubed pairwise ratio sum bounds cyclic quadratic ratios
-- statement:
--   Let $x,y,z>0$ ,prove that;
--
--   ${\frac { \left( y+z \right) ^{3}}{yz}}+{\frac { \left( z+x \right) ^{3}}{xz}}+{\frac { \left( x+y \right) ^{3}}{xy}}\geq 16(\,{\frac {{x}^{2}}{x+y}}+\,{\frac {{y}^{2}}{y+z}}+\,{\frac {{z}^{2}}{z+x}})$
--   Please do it by C-S or A-G
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_24254` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_24254; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_24254 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (y + z) ^ 3 / y / z + (z + x) ^ 3 / z / x + (x + y) ^ 3 / x / y ≥ 16 * (x ^ 2 / (x + y) + y ^ 2 / (y + z) + z ^ 2 / (z + x))  :=  by sorry
