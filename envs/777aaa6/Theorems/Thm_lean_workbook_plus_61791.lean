-- Prove2me | Theorems.Thm_lean_workbook_plus_61791
-- name    : lean_workbook_plus_61791
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/e167288e-5e0e-4503-a0e8-8bd7c58469c9
-- statement:
--   Prove for any $ x,y,z\geq 0$ : \n $ 8(x^3 + y^3 + z^3)^2 \geq 9(x^2 + yz)(y^2 + zx)(z^2 + xy)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61791 (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) : 8 * (x ^ 3 + y ^ 3 + z ^ 3) ^ 2 ≥ 9 * (x ^ 2 + y * z) * (y ^ 2 + z * x) * (z ^ 2 + x * y)   :=  by sorry
