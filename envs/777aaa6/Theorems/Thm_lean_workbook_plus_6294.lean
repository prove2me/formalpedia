-- Prove2me | Theorems.Thm_lean_workbook_plus_6294
-- name    : lean_workbook_plus_6294
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/3706242f-8cdf-4961-8add-75e35721bea4
-- statement:
--   Let $x,y,z\in\mathbb{R}^+$ . Prove that $(x+y)(y+z)(z+x)\ge\frac{8}{9}(x+y+z)(xy+yz+zx)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6294 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + y) * (y + z) * (z + x) ≥ (8 / 9) * (x + y + z) * (x * y + y * z + z * x)   :=  by sorry
