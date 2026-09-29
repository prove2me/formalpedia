-- Prove2me | Theorems.Thm_lean_workbook_plus_76963
-- name    : lean_workbook_plus_76963
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/149a6d7e-a7ad-4988-8bc6-94e6dba28039
-- statement:
--   Use the Ravi Substitution: Since a, b, c are the lengths of a triangle, there are positive reals $ x, y, z$ such that $ a = y+z, b = z+x, c = x+y$ . Prove the inequality becomes: $ \frac{x^3+y^3+z^3+x^2y+y^2z+z^2x-2(xy^2+yz^2+zx^2)}{(x+y)(y+z)(z+x)} \geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76963 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x^3 + y^3 + z^3 + x^2*y + y^2*z + z^2*x - 2*(x*y^2 + y*z^2 + z*x^2)) / (x + y) / (y + z) / (z + x) ≥ 0   :=  by sorry
