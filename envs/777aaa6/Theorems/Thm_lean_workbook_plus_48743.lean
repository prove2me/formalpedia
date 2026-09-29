-- Prove2me | Theorems.Thm_lean_workbook_plus_48743
-- name    : lean_workbook_plus_48743
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/79316a33-0ca8-4e9f-865a-e045e1551cf5
-- statement:
--   Prove that $ 3(x^4y^2 + y^4z^2 + z^4x^2)(x^2y^4 + y^2z^4 + z^2x^4) \geq 3(x^4yz + y^4zx + z^4xy)^2 = 3x^2y^2z^2(x^3 + y^3 + z^3)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48743 (x y z : ℝ) : 3 * (x ^ 4 * y ^ 2 + y ^ 4 * z ^ 2 + z ^ 4 * x ^ 2) * (x ^ 2 * y ^ 4 + y ^ 2 * z ^ 4 + z ^ 2 * x ^ 4) ≥ 3 * (x ^ 4 * y * z + y ^ 4 * z * x + z ^ 4 * x * y) ^ 2   :=  by sorry
