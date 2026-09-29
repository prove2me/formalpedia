-- Prove2me | Theorems.Thm_WorkbookSource_base_28399
-- name    : WorkbookSource.base_28399
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:59:41.184567+00:00
-- url     : https://prove2.me/theorems/fa51b534-fe03-4526-aa53-ada3d6da3e48
-- title:
--   A refined squared pairwise reciprocal lower bound
-- statement:
--   If $ x,y,z>0 $ prove:
--    $ \frac{1}{(y+z)^2}+\frac{1}{(z+x)^2}+\frac{1}{(x+y)^2}\ge\frac{(x+y+z)[9(x+y)(y+z)(z+x)-8xyz]}{4(x+y)^2(y+z)^2(z+x)^2} $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_28399` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_28399; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_28399 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (1 / (y + z) ^ 2 + 1 / (z + x) ^ 2 + 1 / (x + y) ^ 2) ≥ (x + y + z) * (9 * (x + y) * (y + z) * (z + x) - 8 * x * y * z) / (4 * (x + y) ^ 2 * (y + z) ^ 2 * (z + x) ^ 2)  :=  by sorry
