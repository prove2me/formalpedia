-- Prove2me | Theorems.Thm_lean_workbook_plus_78974
-- name    : lean_workbook_plus_78974
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/8de187db-6457-40f3-b35e-2b5077d0f7e6
-- statement:
--   Prove $2\sum x^4 +7\sum y^2z^2\ge 3\sum(y^3z+z^3y)+3\sum x^2yz$ given $x,y,z>0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78974 (x y z : ℝ) : 2 * (x ^ 4 + y ^ 4 + z ^ 4) + 7 * (x ^ 2 * y ^ 2 + x ^ 2 * z ^ 2 + y ^ 2 * z ^ 2) ≥ 3 * (x ^ 3 * y + y ^ 3 * z + z ^ 3 * x) + 3 * (x ^ 2 * y * z + y ^ 2 * z * x + z ^ 2 * x * y)   :=  by sorry
