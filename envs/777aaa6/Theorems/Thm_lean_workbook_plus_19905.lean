-- Prove2me | Theorems.Thm_lean_workbook_plus_19905
-- name    : lean_workbook_plus_19905
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/bf0cf6dd-4118-4ab1-a0ee-977e1775e694
-- statement:
--   Let $x,y,z>0$ Prove that : $x^4+y^4+z^4+xyz\left( x+y+z\right)\ge \frac{2}{3}\left( xy+yz+zx\right)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19905 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x^4 + y^4 + z^4 + x*y*z*(x + y + z) ≥ (2/3)*(x*y + y*z + z*x)^2   :=  by sorry
