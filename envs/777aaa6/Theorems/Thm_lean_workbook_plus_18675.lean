-- Prove2me | Theorems.Thm_lean_workbook_plus_18675
-- name    : lean_workbook_plus_18675
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/ff296fd8-86da-4fb9-885c-160ba7911368
-- statement:
--   Prove that $ 4(yz + zx + xy)^3(x^2y + y^2z + z^2x + xyz)^2\geq27x^2y^2z^2(y + z)^2(z + x)^2(x + y)^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18675 : ∀ x y z : ℝ, 4 * (y * z + z * x + x * y) ^ 3 * (x ^ 2 * y + y ^ 2 * z + z ^ 2 * x + x * y * z) ^ 2 ≥ 27 * x ^ 2 * y ^ 2 * z ^ 2 * (y + z) ^ 2 * (z + x) ^ 2 * (x + y) ^ 2   :=  by sorry
