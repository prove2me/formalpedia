-- Prove2me | Theorems.Thm_lean_workbook_plus_79403
-- name    : lean_workbook_plus_79403
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/d6c24bac-3594-4d5d-a3c6-3e1c7336bba0
-- statement:
--   prove that: $ x^2(x+y)(x+z)+y^2(y+x)(y+z)+z^2(z+x)(z+y)\geq 1+(x+y)^2+(x+z)^2+(y+z)^2 $ given $x,y,z>0$ and $x+y+z=1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79403 : ∀ x y z : ℝ, x > 0 ∧ y > 0 ∧ z > 0 ∧ x + y + z = 1 → x^2 * (x + y) * (x + z) + y^2 * (y + x) * (y + z) + z^2 * (z + x) * (z + y) ≥ 1 + (x + y)^2 + (x + z)^2 + (y + z)^2   :=  by sorry
