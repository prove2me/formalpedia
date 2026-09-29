-- Prove2me | Theorems.Thm_lean_workbook_plus_15267
-- name    : lean_workbook_plus_15267
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/b594ad97-71c2-41c7-8ddd-6e13a7b9b384
-- statement:
--   Prove for any $ x,y,z\geq 0$ : \n $ 8(x^3 + y^3 + z^3)^2 \geq 9(x^2 + yz)(y^2 + zx)(z^2 + xy)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15267 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : 8 * (x ^ 3 + y ^ 3 + z ^ 3) ^ 2 ≥ 9 * (x ^ 2 + y * z) * (y ^ 2 + z * x) * (z ^ 2 + x * y)   :=  by sorry
