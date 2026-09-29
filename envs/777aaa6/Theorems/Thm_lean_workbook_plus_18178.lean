-- Prove2me | Theorems.Thm_lean_workbook_plus_18178
-- name    : lean_workbook_plus_18178
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/1ab9babd-eeab-4390-920a-a758ed93747e
-- statement:
--   Prove or disprove: If $x,y,z$ are the sides of a triangle then $x^3+y^3+z^3+2xyz\ge x^2(y+z)+y^2(x+z)+z^2(y+x)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18178 {x y z : ℝ} (hx : 0 < x ∧ 0 < y ∧ 0 < z) (hx1 : y + z > x) (hx2 : z + x > y) (hx3 : x + y > z) : x ^ 3 + y ^ 3 + z ^ 3 + 2 * x * y * z ≥ x ^ 2 * (y + z) + y ^ 2 * (z + x) + z ^ 2 * (x + y)   :=  by sorry
