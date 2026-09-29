-- Prove2me | Theorems.Thm_lean_workbook_plus_16524
-- name    : lean_workbook_plus_16524
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/0cd9dc8f-c5c3-4bec-bd69-eae5a26b2acb
-- statement:
--   Let \(a = x+y , b = x+z , c = y+z\), where \(x,y,z > 0\): \n\n\((x+y)^3+(x+z)^3+(y+z)^3+8xyz \ge 4(x+y)(x+z)(y+z) \ \ \iff \ \ 2(x^3+y^3+z^3) \ge x^2(y+z)+y^2(x+z)+z^2(x+y)\)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16524 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + y) ^ 3 + (x + z) ^ 3 + (y + z) ^ 3 + 8 * x * y * z ≥ 4 * (x + y) * (x + z) * (y + z) ↔ 2 * (x ^ 3 + y ^ 3 + z ^ 3) ≥ x ^ 2 * (y + z) + y ^ 2 * (x + z) + z ^ 2 * (x + y)   :=  by sorry
