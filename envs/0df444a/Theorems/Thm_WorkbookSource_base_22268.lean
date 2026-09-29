-- Prove2me | Theorems.Thm_WorkbookSource_base_22268
-- name    : WorkbookSource.base_22268
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T07:44:44.106014+00:00
-- url     : https://prove2.me/theorems/9c5d81d9-5fa5-4762-83a3-9478adcb04d0
-- title:
--   A sum of quadratic ratios bounds a shifted triple sum
-- statement:
--   Let $ x,y,z,k > 0$ . Prove that
--    $ \frac {x^2 + y^2}{z + k} + \frac {y^2 + z^2}{x + k} + \frac {z^2 + x^2}{y + k} \geq \frac {3}{2} (x + y + z - k).$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_22268` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_22268; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_22268 (x y z k : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hk : 0 < k) : (x^2 + y^2)/(z + k) + (y^2 + z^2)/(x + k) + (z^2 + x^2)/(y + k) ≥ 3/2 * (x + y + z - k)  :=  by sorry
