-- Prove2me | Theorems.Thm_lean_workbook_plus_9482
-- name    : lean_workbook_plus_9482
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/533fbb10-45cc-4ad7-977a-b35f38b88df9
-- statement:
--   If $ x,y,z>0 $ show that:\n $ \frac{(y+z)(z+x)(x+y)}{4xyz}\ge 1+\frac{x^2+y^2+z^2}{xy+yz+zx} $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9482 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (y + z) * (z + x) * (x + y) / (4 * x * y * z) ≥ 1 + (x ^ 2 + y ^ 2 + z ^ 2) / (x * y + y * z + z * x)   :=  by sorry
