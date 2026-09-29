-- Prove2me | Theorems.Thm_lean_workbook_plus_67230
-- name    : lean_workbook_plus_67230
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/5ff83ec4-d73f-450d-9cab-c8bcd765b378
-- statement:
--   prove that \n\n $\left( {x}^{5}+{y}^{5}+{z}^{5} \right) \left( x+y+z \right) \geq \left( {x}^{2}+{y}^{2}+{z}^{2} \right) \left( {x}^{4}+{y}^{4}+{z}^{4} \right) $ \n\n $\frac{8}{3}\,{\frac { \left( {x}^{2}+{y}^{2}+{z}^{2} \right) ^{2} \left( xy+zx+yz \right) }{ \left( y+z \right) \left( z+x \right) \left( x+y \right) }}\geq \left( \sqrt {{x}^{5}}+\sqrt {{y}^{5}}+\sqrt {{z}^{5}} \right) \left( \sqrt {x}+\sqrt {y}+\sqrt {z} \right) $ \n\n $\frac{3}{2}\,\sum{{\frac {{x}^{3} \left( x+y \right) \left( z+x \right) }{{x}^{2}+yz}}}\geq \left( \sqrt {{x}^{5}}+\sqrt {{y}^{5}}+\sqrt {{z}^{5}} \right) \left( \sqrt {x}+\sqrt {y}+\sqrt {z} \right) $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67230 : ∀ x y z : ℝ, (x ^ 5 + y ^ 5 + z ^ 5) * (x + y + z) ≥ (x ^ 2 + y ^ 2 + z ^ 2) * (x ^ 4 + y ^ 4 + z ^ 4)   :=  by sorry
