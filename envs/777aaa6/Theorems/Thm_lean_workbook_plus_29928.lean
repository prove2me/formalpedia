-- Prove2me | Theorems.Thm_lean_workbook_plus_29928
-- name    : lean_workbook_plus_29928
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/5668f6f4-8783-411b-a11f-48c2b57bd4c1
-- statement:
--   In triangle, prove that $ \left( y-z \right) ^{2} \left( 13\,{x}^{3}+34\,{x}^{2}y+36\,{x}^{2}z+y{z}^{2} \right) + \left( x-z \right) ^{2} \left( {x}^{2}y+3\,{x}^{2}z+5\,{y}^{2}z+9\,x{z}^{2} \right) + \left( x-y \right) ^{4}z+ \left( x-y \right) ^{2} \left( 9\,x{y}^{2}+3\,{x}^{2}y \right) +2\, \left( xy-2\,xz+yz \right) ^{2}y\geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29928 {x y z : ℝ} (hx : x > 0 ∧ y > 0 ∧ z > 0) (hxy : x + y > z) (hxz : x + z > y) (hyz : y + z > x) :  (y - z) ^ 2 * (13 * x ^ 3 + 34 * x ^ 2 * y + 36 * x ^ 2 * z + y * z ^ 2) + (x - z) ^ 2 * (x ^ 2 * y + 3 * x ^ 2 * z + 5 * y ^ 2 * z + 9 * x * z ^ 2) + (x - y) ^ 4 * z + (x - y) ^ 2 * (9 * x * y ^ 2 + 3 * x ^ 2 * y) + 2 * (x * y - 2 * x * z + y * z) ^ 2 * y ≥ 0   :=  by sorry
