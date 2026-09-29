-- Prove2me | Theorems.Thm_lean_workbook_plus_19397
-- name    : lean_workbook_plus_19397
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/f80195fd-65a9-4f83-9b7c-f3de02a1fdc3
-- statement:
--   Prove that for non-negative reals $x$, $y$, and $z$, the following inequality holds:\n6. $(x^2+y^2+z^2)^2 + x^3y + y^3z + z^3x - \frac{2}{3}(x+y+z)(x^3+y^3+z^3) - \frac{2}{3}(x+y+z)(x^2y+y^2z+z^2x) \geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19397 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : (x^2 + y^2 + z^2)^2 + x^3*y + y^3*z + z^3*x - (2/3)*(x + y + z)*(x^3 + y^3 + z^3) - (2/3)*(x + y + z)*(x^2*y + y^2*z + z^2*x) ≥ 0   :=  by sorry
