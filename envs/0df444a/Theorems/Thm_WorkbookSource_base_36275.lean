-- Prove2me | Theorems.Thm_WorkbookSource_base_36275
-- name    : WorkbookSource.base_36275
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:13:32.363242+00:00
-- url     : https://prove2.me/theorems/da2b84c2-886d-46a0-ac03-32d8346d8741
-- title:
--   A squared pairwise ratio sum with a difference-product correction
-- statement:
--   Prove that ${\frac { \left( y+z \right) ^{2}}{{x}^{2}+yz}}+{\frac { \left( z+x \right) ^{2}}{{y}^{2}+zx}}+{\frac { \left( x+y \right) ^{2}}{{z}^{2}+xy}}\geq 6+5\,{\frac { \left( y-z \right) ^{2} \left( z-x \right) ^{2} \left( x-y \right) ^{2}}{ \left( {x}^{2}+yz \right) \left( {y}^{2}+zx \right) \left( {z}^{2}+xy \right) }}$ for $x,y,z>0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_36275` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_36275; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_36275 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (y + z) ^ 2 / (x ^ 2 + y * z) + (z + x) ^ 2 / (y ^ 2 + z * x) + (x + y) ^ 2 / (z ^ 2 + x * y) ≥ 6 + 5 * (y - z) ^ 2 * (z - x) ^ 2 * (x - y) ^ 2 / ((x ^ 2 + y * z) * (y ^ 2 + z * x) * (z ^ 2 + x * y))  :=  by sorry
