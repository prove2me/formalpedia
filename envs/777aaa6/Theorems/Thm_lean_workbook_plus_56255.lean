-- Prove2me | Theorems.Thm_lean_workbook_plus_56255
-- name    : lean_workbook_plus_56255
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/754176e9-f7aa-491f-87f9-9ef38ec51c91
-- statement:
--   Prove that for non-negative reals $x$, $y$, and $z$, the following inequalities hold:\n1. $(xy+zx+yz)^2 + (x+y+z)^2(x^2+y^2+z^2) - 4(x+y+z)(x^2y+yz^2+zx^2) \geq 0$\n2. $(x+y+z)^4 + (x^2+y^2+z^2)(xy+zx+yz) - \frac{15}{2}(x+y+z)(x^2y+y^2z+z^2x) - \frac{15}{2}(x+y+z)xyz \geq 0$\n3. $(x+y+z)^4 + y^2x^2 + y^2z^2 + z^2x^2 - 7(x+y+z)(x^2y+y^2z+z^2x) - 7(x+y+z)xyz \geq 0$\n4. $(x+y+z)^4 + (x+y+z)(x^2y+y^2z+z^2x) - \frac{10}{3}(x+y+z)(y+z)(z+x)(x+y) - \frac{10}{3}x^3y - \frac{10}{3}y^3z - \frac{10}{3}z^3x \geq 0$\n5. $(x+y+z)^4 + (x^2+y^2+z^2)(xy+zx+yz) - \frac{15}{2}(xy+zx+yz)^2 - \frac{15}{2}x^3y - \frac{15}{2}y^3z - \frac{15}{2}z^3x \geq 0$\n6. $(x^2+y^2+z^2)^2 + x^3y + y^3z + z^3x - \frac{2}{3}(x+y+z)(x^3+y^3+z^3) - \frac{2}{3}(x+y+z)(x^2y+y^2z+z^2x) \geq 0$\n7. $(x+y+z)(x^3+y^3+z^3) + (x+y+z)(y+z)(z+x)(x+y) - \frac{11}{2}(x+y+z)xyz - \frac{11}{2}x^3y - \frac{11}{2}y^3z - \frac{11}{2}z^3x \geq 0$\n8. $(x+y+z)^4 + y^2x^2 + y^2z^2 + z^2x^2 - 7(xy+zx+yz)^2 - 7x^3y - 7y^3z - 7z^3x \geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56255 :  ∀ x y z : ℝ, (x * y + z * x + y * z) ^ 2 + (x + y + z) ^ 2 * (x ^ 2 + y ^ 2 + z ^ 2) - 4 * (x + y + z) * (x ^ 2 * y + y * z ^ 2 + z * x ^ 2) ≥ 0   :=  by sorry
