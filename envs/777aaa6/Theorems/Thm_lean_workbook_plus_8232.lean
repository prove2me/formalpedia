-- Prove2me | Theorems.Thm_lean_workbook_plus_8232
-- name    : lean_workbook_plus_8232
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/f984c119-b453-44b3-b686-cf90a304bf13
-- statement:
--   Show that for nonnegative x, y, and z one has the bound\n$x^2y^3$ + $x^2z^3$ + $y^2x^3$ + $y^2z^3$ + $z^2x^3$ + $z^2y^3$ \n≤ $xy^4$ + $xz^4$ + $yx^4$ + $yz^4$ + $zx^4$ + $zy^4$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8232 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : x^2*y^3 + x^2*z^3 + y^2*x^3 + y^2*z^3 + z^2*x^3 + z^2*y^3 ≤ x*y^4 + x*z^4 + y*x^4 + y*z^4 + z*x^4 + z*y^4   :=  by sorry
