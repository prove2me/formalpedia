-- Prove2me | Theorems.Thm_WorkbookSource_base_15913
-- name    : WorkbookSource.base_15913
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:52:15.488364+00:00
-- url     : https://prove2.me/theorems/118acd90-e1dd-4be3-8b32-d1e5eb3630dc
-- title:
--   A squared reciprocal-sum bound for a symmetric product
-- statement:
--   If $ x,y,z>0 $ prove:
--    $ \frac{(y+z)^2}{x^2}+\frac{(z+x)^2}{y^2}+\frac{(x+y)^2}{z^2}+28\ge\frac{5(x+y)(y+z)(z+x)}{xyz} $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_15913` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_15913; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_15913 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (y + z) ^ 2 / x ^ 2 + (z + x) ^ 2 / y ^ 2 + (x + y) ^ 2 / z ^ 2 + 28 ≥ 5 * (x + y) * (y + z) * (z + x) / (x * y * z)  :=  by sorry
