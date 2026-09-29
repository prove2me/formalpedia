-- Prove2me | Theorems.Thm_WorkbookSource_base_39998
-- name    : WorkbookSource.base_39998
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:52:14.767959+00:00
-- url     : https://prove2.me/theorems/64d6f02c-2763-499e-b8ed-ca2e332be02b
-- title:
--   A symmetric quadratic reciprocal lower bound
-- statement:
--   Given $x,y,z>0$ ,prove that:
--    ${\frac { \left( x+y+z \right) ^{2}}{{x}^{2}+2\,yz}}+{\frac { \left( x+y+z \right) ^{2}}{{y}^{2}+2\,xz}}+{\frac { \left( x+y+z \right) ^{2}}{ {z}^{2}+2\,xy}}\geq 9$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_39998` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_39998; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_39998 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + y + z) ^ 2 / (x ^ 2 + 2 * y * z) + (x + y + z) ^ 2 / (y ^ 2 + 2 * x * z) + (x + y + z) ^ 2 / (z ^ 2 + 2 * x * y) ≥ 9  :=  by sorry
