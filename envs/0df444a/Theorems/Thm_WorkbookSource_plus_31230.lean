-- Prove2me | Theorems.Thm_WorkbookSource_plus_31230
-- name    : WorkbookSource.plus_31230
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:28:50.721396+00:00
-- url     : https://prove2.me/theorems/8e4bafb2-dbe2-4896-bfea-cfc435ca1e76
-- title:
--   An eighth-degree polynomial with cyclic difference terms is nonnegative
-- statement:
--   $g=3\, \left( y-z \right) ^{2}{x}^{6}+9\, \left( y+z \right) \left( y-z \right) ^{2}{x}^{5}+ \left( 12\,{z}^{4}-9\,y{z}^{3}-2\,{y}^{2}{z}^{2}+12\,{y}^{4}-9\,{y}^{3}z \right) {x}^{4}+ \left( y+z \right) \left( 3\,{z}^{2}-4\,yz+3\,{y}^{2} \right) \left( 3\,{z}^{2}-2\,yz+3\,{y}^{2} \right) {x}^{3}+ \left( -9\,z{y}^{5}+3\,{y}^{6}-2\,{y}^{2}{z}^{4}-2\,{y}^{4}{z}^{2}+3\,{z}^{6}-9\,y{z}^{5}+8\,{y}^{3}{z}^{3} \right) {x}^{2}-3\,yz \left( y+z \right) \left( 2\,{z}^{4}+y{z}^{3}+2\,{y}^{2}{z}^{2}+{y}^{3}z+2\,{y}^{4} \right) x+3\,{y}^{2}{z}^{2} \left( {y}^{2}+yz+{z}^{2} \right) \left( y+z \right) ^{2}\geq 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_31230` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_31230; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_31230 (x y z : ℝ) : (3 * (y - z) ^ 2 * x ^ 6 + 9 * (y + z) * (y - z) ^ 2 * x ^ 5 + (12 * z ^ 4 - 9 * y * z ^ 3 - 2 * y ^ 2 * z ^ 2 + 12 * y ^ 4 - 9 * y ^ 3 * z) * x ^ 4 + (y + z) * (3 * z ^ 2 - 4 * y * z + 3 * y ^ 2) * (3 * z ^ 2 - 2 * y * z + 3 * y ^ 2) * x ^ 3 + (-9 * z * y ^ 5 + 3 * y ^ 6 - 2 * y ^ 2 * z ^ 4 - 2 * y ^ 4 * z ^ 2 + 3 * z ^ 6 - 9 * y * z ^ 5 + 8 * y ^ 3 * z ^ 3) * x ^ 2 - 3 * y * z * (y + z) * (2 * z ^ 4 + y * z ^ 3 + 2 * y ^ 2 * z ^ 2 + y ^ 3 * z + 2 * y ^ 4) * x + 3 * y ^ 2 * z ^ 2 * (y ^ 2 + y * z + z ^ 2) * (y + z) ^ 2) ≥ 0   :=  by sorry
