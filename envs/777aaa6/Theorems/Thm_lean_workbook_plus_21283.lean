-- Prove2me | Theorems.Thm_lean_workbook_plus_21283
-- name    : lean_workbook_plus_21283
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/66ce18b9-33ad-4f0d-9690-4dfc5dda528d
-- statement:
--   ${\frac {{x}^{2}+yz}{{y}^{2}+{z}^{2}}}+{\frac {{y}^{2}+xz}{{x}^{2}+{z}^{2}}}+{\frac {{z}^{2}+xy}{{y}^{2}+{x}^{2}}}\geq 5/2+4\,{\frac {xyz}{ \left( y+z \right) \left( z+x \right) \left( x+y \right) }}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21283 : ∀ x y z : ℝ, (x ^ 2 + y * z) / (y ^ 2 + z ^ 2) + (y ^ 2 + x * z) / (x ^ 2 + z ^ 2) + (z ^ 2 + x * y) / (y ^ 2 + x ^ 2) ≥ 5 / 2 + 4 * (x * y * z) / ((y + z) * (z + x) * (x + y))   :=  by sorry
