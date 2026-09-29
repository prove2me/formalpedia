-- Prove2me | Theorems.Thm_lean_workbook_plus_35983
-- name    : lean_workbook_plus_35983
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/0416a286-d410-49b8-b428-299533bd995c
-- statement:
--   Replace $(a,b,c) \to (x+y,y+z,z+x)$ your inequality become\n $5(x^3+y^3+z^3) +19(x^2y+y^2z+z^2x) \geqslant 30xyz + 14(xy^2+yz^2+zx^2),$ equivalent to\n $\sum\frac{(x^2+9y^2+50yz)(x-y)^2}{2(x+y+z)} \geqslant 0.$ Done.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35983 :
  ∀ x y z : ℝ,
    5 * (x^3 + y^3 + z^3) + 19 * (x^2 * y + y^2 * z + z^2 * x) ≥ 30 * x * y * z + 14 * (x * y^2 + y * z^2 + z * x^2)   :=  by sorry
