-- Prove2me | Theorems.Thm_lean_workbook_plus_25137
-- name    : lean_workbook_plus_25137
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/83bc0d70-ffca-4737-8248-574bb28716e3
-- statement:
--   Prove that $x^4y^2+x^2y^4+y^4z^2+y^2z^4+z^4x^2+z^2x^4+2(x^3y^3+y^3z^3+z^3x^3) \geq 2xyz(x^3+y^3+z^3)+6x^2y^2z^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25137 :  ∀ x y z : ℝ, x ^ 4 * y ^ 2 + x ^ 2 * y ^ 4 + y ^ 4 * z ^ 2 + y ^ 2 * z ^ 4 + z ^ 4 * x ^ 2 + z ^ 2 * x ^ 4 + 2 * (x ^ 3 * y ^ 3 + y ^ 3 * z ^ 3 + z ^ 3 * x ^ 3) ≥ 2 * x * y * z * (x ^ 3 + y ^ 3 + z ^ 3) + 6 * x ^ 2 * y ^ 2 * z ^ 2   :=  by sorry
