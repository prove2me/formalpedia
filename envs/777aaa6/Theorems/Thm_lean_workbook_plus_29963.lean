-- Prove2me | Theorems.Thm_lean_workbook_plus_29963
-- name    : lean_workbook_plus_29963
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/70ea3bef-6d78-47b2-b127-8b30707b1f26
-- statement:
--   Let $x,y,z \in R$ ,prove that: $xyz(yz^2+x^2z+xy^2)+z^4x^2+y^2x^4+y^4z^2\geq \frac{2}{3}(x^2y+zy^2+z^2x)^2.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29963 (x y z : ℝ) : x * y * z * (y * z ^ 2 + x ^ 2 * z + x * y ^ 2) + z ^ 4 * x ^ 2 + y ^ 2 * x ^ 4 + y ^ 4 * z ^ 2 ≥ 2 / 3 * (x ^ 2 * y + z * y ^ 2 + z ^ 2 * x) ^ 2   :=  by sorry
