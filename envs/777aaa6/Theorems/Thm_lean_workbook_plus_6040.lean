-- Prove2me | Theorems.Thm_lean_workbook_plus_6040
-- name    : lean_workbook_plus_6040
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/cd171729-c754-44be-8138-fbb776ec4135
-- statement:
--   Let $(a;b;c)=(\frac{2x^2}{yz};\frac{2y^2}{zx};\frac{2z^2}{xy})$ \nNeed to prove: $$4\,{\frac {{y}^{2}{z}^{2}{x}^{2} \left( x+y+z \right) ^{2} \left( {x}^{2}-xy-zx+{y}^{2}-yz+{z}^{2} \right) ^{2}}{ \left( 2\,{x}^{2}+yz \right) ^{2} \left( zx+2\,{y}^{2} \right) ^{2} \left( xy+2\,{z}^{2} \right) ^{2}}} \geqq 0$$ Done.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6040 :  ∀ x y z : ℝ, (4 * (y^2 * z^2 * x^2 * (x + y + z)^2 * (x^2 - x * y - x * z + y^2 - y * z + z^2)^2) / ((2 * x^2 + y * z)^2 * (z * x + 2 * y^2)^2 * (x * y + 2 * z^2)^2)) ≥ 0   :=  by sorry
