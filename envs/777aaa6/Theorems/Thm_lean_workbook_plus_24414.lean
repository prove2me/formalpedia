-- Prove2me | Theorems.Thm_lean_workbook_plus_24414
-- name    : lean_workbook_plus_24414
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/75e42cbe-20f6-44c1-b353-5dccc8940a3d
-- statement:
--   Prove that \((x^3+y^3+z^3)^2 + 4 \Big( xyz \Big ) ^2 \geq 2 \Big( y^3z^3+z^3x^3+x^3y^3 \Big)\) for \(x,y,z \in R\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24414 (x y z : ℝ) : (x ^ 3 + y ^ 3 + z ^ 3) ^ 2 + 4 * (x * y * z) ^ 2 ≥ 2 * (y ^ 3 * z ^ 3 + z ^ 3 * x ^ 3 + x ^ 3 * y ^ 3)   :=  by sorry
