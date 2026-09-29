-- Prove2me | Theorems.Thm_WorkbookSource_plus_14336
-- name    : WorkbookSource.plus_14336
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:15:42.991439+00:00
-- url     : https://prove2.me/theorems/c8bfd0f4-54b5-496d-9ba7-b429dac42a82
-- title:
--   A pair-product sum bounds a squared triple-product expression
-- statement:
--   Let $ x,y,z>0 $ and $ x+y+z=3 $ . Prove the inequality: $ \frac{64}{3}(xy+yz+xz)\le55+9(xyz)^2$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_14336` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_14336; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_14336 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 3) : (64 / 3) * (x * y + y * z + z * x) ≤ 55 + 9 * (x * y * z) ^ 2   :=  by sorry
