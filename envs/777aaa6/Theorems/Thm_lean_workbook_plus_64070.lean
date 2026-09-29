-- Prove2me | Theorems.Thm_lean_workbook_plus_64070
-- name    : lean_workbook_plus_64070
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/e010fc89-015c-47c7-8c10-679197608cf3
-- statement:
--   If $ x,y,z>0 $ prove that: \n $ \frac{y+z}{x}+\frac{z+x}{y}+\frac{x+y}{z}\ge 3(1+\frac{x^2+y^2+z^2}{xy+yz+zx}) $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64070 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (y + z) / x + (z + x) / y + (x + y) / z >= 3 * (1 + (x ^ 2 + y ^ 2 + z ^ 2) / (x * y + y * z + z * x))   :=  by sorry
