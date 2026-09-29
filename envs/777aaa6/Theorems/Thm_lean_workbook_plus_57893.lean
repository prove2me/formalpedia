-- Prove2me | Theorems.Thm_lean_workbook_plus_57893
-- name    : lean_workbook_plus_57893
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/e3360d1e-9df0-40bd-b228-979c3aaa016e
-- statement:
--   Let $x,y,z \in R$ ,prove that: $z^4x^2+x^4y^2+y^4z^2\geq \frac{1}{3}(x^2y+zy^2+z^2x)^2.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57893 (x y z : ℝ) : z ^ 4 * x ^ 2 + x ^ 4 * y ^ 2 + y ^ 4 * z ^ 2 ≥ 1 / 3 * (x ^ 2 * y + z * y ^ 2 + z ^ 2 * x) ^ 2   :=  by sorry
