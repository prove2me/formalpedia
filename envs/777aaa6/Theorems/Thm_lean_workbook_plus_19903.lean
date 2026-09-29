-- Prove2me | Theorems.Thm_lean_workbook_plus_19903
-- name    : lean_workbook_plus_19903
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/bbf43b0b-c730-43d6-a719-d93d26869462
-- statement:
--   More stronger is: \n $ \left( {x}^{2}+{y}^{2} \right) \left( {y}^{2}+{z}^{2} \right) \left( {x}^{2}+{z}^{2} \right) \left( xy+xz+yz \right) ^{2} \left( x+y+z \right) ^{2}\geq 8\, \left( x{y}^{2}+y{z}^{2}+{x}^{2}z \right) ^{2} \left( {x}^{2}y+{y}^{2}z+{z}^{2}x \right) ^{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19903 :  ∀ x y z : ℝ, (x^2 + y^2) * (y^2 + z^2) * (x^2 + z^2) * (x * y + x * z + y * z)^2 * (x + y + z)^2 ≥ 8 * (x * y^2 + y * z^2 + x^2 * z)^2 * (x^2 * y + y^2 * z + z^2 * x)^2   :=  by sorry
