-- Prove2me | Theorems.Thm_RybinAI2026_P01_quadratic_nonneg_of_sq_eq_mul
-- name    : RybinAI2026.P01.quadratic_nonneg_of_sq_eq_mul
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-02T01:32:53.517985+00:00
-- url     : https://prove2.me/theorems/c1cf0821-e093-43da-a2f1-5a020021a5cd
-- title:
--   A quadratic with equal square roots is nonnegative
-- statement:
--   For real X, Y, Z, lam with X, Y, Z nonnegative and X*Y = Z^2, the quadratic X - 2 lam Z + lam^2 Y is nonnegative for every real lam.  When Y > 0 the identity Y*(X - 2 lam Z + lam^2 Y) = (Z - lam Y)^2 and Y > 0 give the claim; when Y = 0 the hypothesis forces Z = 0 and the expression reduces to X >= 0.
-- source:
--   P01 mission c36fd4df-ef29-4fbc-9bb6-1f6acf3c0733, root 8d67c9ac-a6c7-418c-b8db-0bc029c18484. Scalar core of the two-direction Cauchy-Schwarz step one_sphere_cross_excess_cs_step (81ec1479); it replaces the sqrt-rewrite chain that failed in candidates 6120-6143.

import Mathlib

namespace RybinAI2026.P01

/-- A quadratic with `Z ^ 2 = X * Y` and nonnegative coefficients is nonnegative. -/
theorem quadratic_nonneg_of_sq_eq_mul {X Y Z lam : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (hZ : 0 ≤ Z)
    (h : X * Y = Z ^ 2) : 0 ≤ X - 2 * lam * Z + lam ^ 2 * Y := by sorry

end RybinAI2026.P01
