-- Prove2me | solution 1 for lean_workbook_plus_75474
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:03:44.638544+00:00
-- url     : https://prove2.me/submissions/ee868f41-6d2d-477e-bce7-35ac165824ed

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c : ℝ) :
    (a^2 + b^2 + c^2)^2 - 2 * (a^3 * b + b^3 * c + c^3 * a) ≥
      2 * a * b * c * (a + b + c) - (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) := by
  nlinarith only [sq_nonneg (a^2-a*b), sq_nonneg (b^2-b*c), sq_nonneg (c^2-c*a),
    sq_nonneg (a*(b-c)), sq_nonneg (b*(c-a)), sq_nonneg (c*(a-b))]

#print axioms solution
